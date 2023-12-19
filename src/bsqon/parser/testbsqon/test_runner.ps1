#!/usr/bin/powershell -Command

# get the directory of this script
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Definition

# get the test data directory
$testDataDir = Join-Path $scriptDir "\tests"

# get the bsqon executable
$bsqonExe = Join-Path $scriptDir "..\..\..\..\build\output\bsqon"

# get the metadata generation script
$metadataGenScript = Join-Path $scriptDir "..\..\..\..\bin\frontend\generate_metadata.js"

########
# Setup the test directory as needed
$testOutputDir = Join-Path $scriptDir "..\..\..\..\build\test\bsqon"

New-Item -Path $testOutputDir -ItemType Directory -Force | Out-Null

$totalTests = 0
$errorTests = 0
$passingTests = 0
$failingTests = 0

# function for running a single test
function RunTest($testName, $testType, $testFile, $metadataFile, $expectedFile, $tmpFile)
{
    $process = Start-Process -FilePath $bsqonExe -RedirectStandardOutput $tmpFile -ArgumentList "$metadataFile $testType $testFile" -PassThru -Wait

    if($process.ExitCode -ne 0) {
        Write-Host "Failed to parse '$testName'"
        Write-Host (Get-Content $tmpFile -Raw -Encoding utf8)
        $errorTests += 1
    }
    else {
        $diff = Compare-Object -ReferenceObject (Get-Content $expectedFile -Raw -Encoding utf8) -DifferenceObject (Get-Content $tmpFile -Raw -Encoding utf8)
        if ($diff) {
            Write-Host "Parse output does not match expected '$testName'"
            Write-Host "--diff--"
            Write-Host $diff
            $failingTests += 1
        }
        else {
            $passingTests += 1
            Write-Host "Test '$testName' passed"
        }
    }
}

function RunTestSuite($testName)
{
    $srcList = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File | Where-Object { $_.Extension -eq ".bsq" -or $_.Extension -eq ".bsqapi" }
    
    if($srcList.Count -eq 0) {
        Write-Host "No source files found for test suite '$testName'"
        return
    }

    $tests = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File -Filter "*.bsqon" | Where-Object { $_.Name -notmatch '_expected.bsqon$' }

    $metadataFile = New-Item -Path (Join-Path $testOutputDir $testName "metadata.json") -ItemType File -Force
    $tmpFile = New-Item -Path (Join-Path $testOutputDir $testName "_output_.bsqon") -ItemType File -Force

    node $metadataGenScript --outdir (Join-Path $testOutputDir $testName) $srcList | Out-Null
    if (-Not ($?)) {
        Write-Host "Failed to generate metadata for '$testName'"
        $errorTests += 1
    }
    else {
        ForEach ($test in $tests) {
            $totalTests += 1
            $contents = Get-Content -Path $test.FullName -Encoding utf8 -TotalCount 10

            if($contents[0] -notmatch '^\s*%%\s*[A-Z].+') {
                Write-Host "Test '$testName' does not have a type specified at the top of the file"
                $errorTests += 1
                continue
            }
            
            $testType = $contents[0].Trim().Substring(2).Trim()
            $expected = $test.FullName.Replace(".bsqon", "_expected.bsqon")

            if(-Not (Test-Path $expected)) {
                Write-Host "Test '$testName' has no expected result file"
                $errorTests += 1
                continue
            }

            RunTest $testName $testType $test $metadataFile $expected $tmpFile
        }

        #cleanup here
    }

    #cleanup here
}

RunTestSuite("doit")

return