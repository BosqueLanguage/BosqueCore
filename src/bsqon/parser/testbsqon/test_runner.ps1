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

        $SCRIPT:failingTests += 1
    }
    else {
        $actualContent = (Get-Content $tmpFile -Raw -Encoding utf8).Trim()
        $expectedContent = (Get-Content $expectedFile -Raw -Encoding utf8).Trim()

        if ($actualContent -cne $expectedContent) {
            Write-Host "  Parse output does not match expected for test '$testName'" -ForegroundColor Red
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

function RunErrorTest($testName, $testType, $testFile, $metadataFile, $expectedFile, $tmpFile)
{
    $process = Start-Process -FilePath $bsqonExe -RedirectStandardOutput $tmpFile -ArgumentList "$metadataFile $testType $testFile" -PassThru -Wait

    if($process.ExitCode -eq 0) {
        Write-Host "  Expected error in parse of $testName" -ForegroundColor Red

        $actualContent = (Get-Content $tmpFile -Raw -Encoding utf8).Trim()
        Write-Host "output: $actualContent"

        $SCRIPT:failingTests += 1
    }
    else {
        $actualContent = (Get-Content $tmpFile -Raw -Encoding utf8).Trim()
        $expectedContent = (Get-Content $expectedFile -Raw -Encoding utf8).Trim()

        if ($actualContent -cne $expectedContent) {
            Write-Host "  Parse output does not match expected for test '$testName'" -ForegroundColor Red
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
    $srcList = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File | Where-Object { $_.Extension -eq ".bsq" -or $_.Extension -eq ".bsqapi" }
    
    if($srcList.Count -eq 0) {
        Write-Host "  No source files found for test suite $testName" -ForegroundColor Red
        return
    }

    $tests = Get-ChildItem -Path (Join-Path $testDataDir $testName) -File -Filter "*.bsqon" | Where-Object { $_.Name -notmatch '_expected.bsqon$' }

    Write-Host "------------"
    Write-Host "Running test suite $testName..."
    $oldFails = $errorTests + $failingTests

    $metadataFile = New-Item -Path (Join-Path $testOutputDir $testName "metadata.json") -ItemType File -Force
    $tmpFile = New-Item -Path (Join-Path $testOutputDir $testName "_output_.bsqon") -ItemType File -Force

    node $metadataGenScript --outdir (Join-Path $testOutputDir $testName) $srcList | Out-Null

    if (-Not ($?)) {
        Write-Host "  Failed to generate metadata for $testName" -ForegroundColor Red
        $SCRIPT:errorTests += 1
    }
    else {
        ForEach ($test in $tests) {
            $SCRIPT:totalTests += 1
            $tname = $test.BaseName
            $contents = Get-Content -Path $test.FullName -Encoding utf8 -TotalCount 10

            if($contents[0] -notmatch '^\s*%%\s*[A-Z].+') {
                Write-Host "  Test $tname does not have a type specified at the top of the file" -ForegroundColor Red
                $SCRIPT:errorTests += 1
                continue
            }
            
            $testType = $contents[0].Trim().Substring(2).Trim()
            $expected = $test.FullName.Replace(".bsqon", "_expected.bsqon")

            if(-Not (Test-Path $expected)) {
                Write-Host "  Test $tname has no expected result file" -ForegroundColor Red
                $SCRIPT:errorTests += 1
                continue
            }

            if ($testName.EndsWith("_errors")) {
                RunErrorTest $test.BaseName $testType $test $metadataFile $expected $tmpFile
            }
            else {
                RunTest $test.BaseName $testType $test $metadataFile $expected $tmpFile
            }
        }

        Remove-Item -Path $tmpFile.FullName -Force | Out-Null
    }

    Remove-Item -Path (Join-Path $testOutputDir $testName) -Recurse | Out-Null

    if ($oldFails -eq ($errorTests + $failingTests)) {
        Write-Host "...all tests passed" -ForegroundColor Green
    }
    else {
        Write-Host "...$(($failingTests + $errorTests) - $oldFails) new failures" -ForegroundColor Red
    }
}

$allsuites = Get-ChildItem -Path $testDataDir -Directory
ForEach ($suite in $allsuites) {
    RunTestSuite($suite.Name)
}

Write-Host "------------"
Write-Host "Total tests:   $totalTests"
Write-Host "Passing tests: $passingTests"

if($totalTests -eq $passingTests) {
    Write-Host "...all passed!" -NoNewline -ForegroundColor Green
}

if($errorTests -gt 0) {
    Write-Host "Error tests: $errorTests" -NoNewline -ForegroundColor Magenta

    if($failingTests -gt 0) {
        Write-Host ""
    }
}

if($failingTests -gt 0) {
    Write-Host "Failing tests: $failingTests" -NoNewline -ForegroundColor Red
}

Write-Host ""
