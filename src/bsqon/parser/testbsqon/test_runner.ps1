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
function RunTest($testName, $testType, $testData, $expectedResult, $testOutputDirectory, $srcList)
{
    node $metadataGenScript --outdir $testOutputDirectory.FullName $srcList | Out-Null
    if (-Not ($?)) {
        Write-Host "Failed to generate metadata for '$testName'"
        $errorTests += 1
    }
    else {
        $process = Start-Process -FilePath $bsqonExe -ArgumentList "$testOutputDirectory.FullName\metadata.json $testType $testData.FullName"
        $process.StandardInput.Write($testData)
        $process.StandardInput.Close()

        $result = $process.StandardOutput.ReadToEnd()
        $process.WaitForExit()

        if($process.ExitCode -ne 0) {
            Write-Host "Failed to parse '$testName'"
            Write-Host $result
            $errorTests += 1
        }
        else {
            $expected = Get-Content -Path $expectedResult -Raw -Encoding utf8
            $diff = Compare-Object -ReferenceObject $result -DifferenceObject $expected
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
}

function RunTestSuite($testName)
{
    $testOutputDir = New-Item -Path (Join-Path $testOutputDir $testName) -ItemType Directory -Force
    $srcList = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File | Where-Object { $_.Extension -eq ".bsq" -or $_.Extension -eq ".bsqapi" }
    
    if($srcList.Count -eq 0) {
        Write-Host "No source files found for test suite '$testName'"
        return
    }

    $tests = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File -Filter "*.bsqon" | Where-Object { $_.Name -notmatch '_expected.bsqon$' }
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

        RunTest $testName $testType $test $expected $testOutputDir $srcList
    }

    #cleanup here
}

RunTestSuite("doit")
