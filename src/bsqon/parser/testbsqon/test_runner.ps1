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
        Write-Host "  Failed to parse $testName" -ForegroundColor Red
        Write-Host (Get-Content $tmpFile -Raw -Encoding utf8) -ForegroundColor Gray

        $SCRIPT:errorTests += 1
    }
    else {
        $actualContent = (Get-Content $tmpFile -Raw -Encoding utf8).Trim()
        $expectedContent = (Get-Content $expectedFile -Raw -Encoding utf8).Trim()

        if ($actualContent -ne $expectedContent) {
            Write-Host "  Parse output does not match expected $testName" -ForegroundColor Red
            Write-Host "expected: $expectedContent"
            Write-Host "actual:   " -NoNewline
            Write-Host $actualContent -ForegroundColor Gray

            $SCRIPT:failingTests += 1
        }
        else {
            Write-Host "  Test $testName " -NoNewline
            Write-Host "passed" -ForegroundColor Green

            $SCRIPT:passingTests += 1
        }
    }
}

function RunTestSuite($testName)
{
    Write-Host "------------"
    Write-Host "Running test suite $testName"
    $oldFails = $errorTests + $failingTests

    $srcList = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File | Where-Object { $_.Extension -eq ".bsq" -or $_.Extension -eq ".bsqapi" }
    
    if($srcList.Count -eq 0) {
        Write-Host "  No source files found for test suite $testName" -ForegroundColor Red
        return
    }

    $tests = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File -Filter "*.bsqon" | Where-Object { $_.Name -notmatch '_expected.bsqon$' }

    $metadataFile = New-Item -Path (Join-Path $testOutputDir $testName "metadata.json") -ItemType File -Force
    $tmpFile = New-Item -Path (Join-Path $testOutputDir $testName "_output_.bsqon") -ItemType File -Force

    node $metadataGenScript --outdir (Join-Path $testOutputDir $testName) $srcList | Out-Null

    if (-Not ($?)) {
        Write-Host "  Failed to generate metadata for $testName" -ForegroundColor Red
        $errorTests += 1
    }
    else {
        ForEach ($test in $tests) {
            $totalTests += 1
            $contents = Get-Content -Path $test.FullName -Encoding utf8 -TotalCount 10

            if($contents[0] -notmatch '^\s*%%\s*[A-Z].+') {
                Write-Host "  Test $testName does not have a type specified at the top of the file" -ForegroundColor Red
                $errorTests += 1
                continue
            }
            
            $testType = $contents[0].Trim().Substring(2).Trim()
            $expected = $test.FullName.Replace(".bsqon", "_expected.bsqon")

            if(-Not (Test-Path $expected)) {
                Write-Host "  Test $testName has no expected result file" -ForegroundColor Red
                $errorTests += 1
                continue
            }

            RunTest $testName $testType $test $metadataFile $expected $tmpFile
        }

        Remove-Item -Path $tmpFile.FullName -Force | Out-Null
    }

    Remove-Item -Path (Join-Path $testDataDir $testName) -Recurse | Out-Null

    Write-Output $oldFails
    Write-Output ($errorTests + $failingTests) 

    if ($oldFails -eq ($errorTests + $failingTests)) {
        Write-Host "...all tests passed" -ForegroundColor Green
    }
    else {
        Write-Host "..."(($failingTests + $errorTests) - $oldFails)"new failures" -ForegroundColor Red
    }
}

RunTestSuite("doit")

return