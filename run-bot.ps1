

function run-botonce2 { 
    Param(
        $name, 
        $game, 
        [switch]$public, 
        [switch]$right, 
        $privateGame, 
        [switch]$noui,
        $path = "C:\generals-bot\bot_ek0x45.py",
        $userID = $null
    )
    $df = Get-Date -format yyyy-MM-dd_hh-mm-ss 
    $arguments = [System.Collections.ArrayList]::new()
    if ($privateGame) {
        $game = "private"
        [void] $arguments.Add("--roomID")
        [void] $arguments.Add($privateGame)
    }
    if ($userID) {
        [void] $arguments.Add("--userid")
        [void] $arguments.Add($userID)
    }
    if ($right) { [void] $arguments.Add("--right") }
    if ($noui) { [void] $arguments.Add("--no-ui") }
    if ($public) { 
        [void] $arguments.Add("--public")
    }
    $argString = $([string]::Join(" ", $arguments))
    Write-Verbose $argString -Verbose
    Start-Transcript -path "H:\GeneralsLogs\$name-$game-$df$privateGame.txt"
    try {
        Write-Verbose "C:\Python36-32\python.exe $path -name $name -g $game $argString" -verbose
        C:\Python36-32\python.exe "$path" -name $name -g $game @arguments 2>&1 
    } 
    catch 
    {
        Write-Error $_
    }
    finally 
    {
        stop-transcript
    }
    PING 127.0.0.1 -n 1 | out-null
	Get-ChildItem "H:\GeneralsLogs" -Recurse | ? { $_.LastWriteTime -lt (get-date).AddMinutes(-30) } | Remove-Item -Force -Recurse -ErrorAction Ignore
}

function run-botonce { 
    Param(
        $name, 
        $game, 
        [switch]$public, 
        [switch]$right, 
        $privateGame, 
        [switch]$noui,
        $path = "C:\generals-bot\bot_ek0x45.py",
        $userID = $null,
		[switch]$nolog
    )
    $df = Get-Date -format yyyy-MM-dd_hh-mm-ss 
    $arguments = [System.Collections.ArrayList]::new()
    if ($privateGame) {
        $game = "private"
        [void] $arguments.Add("--roomID")
        [void] $arguments.Add($privateGame)
    }
    if ($userID) {
        [void] $arguments.Add("--userid")
        [void] $arguments.Add($userID)
    }
    if ($right) { [void] $arguments.Add("--right") }
    if ($noui) { [void] $arguments.Add("--no-ui") }
    if ($public) { 
        [void] $arguments.Add("--public")
    }
	$arguments = $arguments.ToArray()
    $argString = $([string]::Join(" ", $arguments))
    Write-Verbose $argString -Verbose

	$exeString = @"
	`$name = '$name'
	`$game = '$game'
	`$df = '$df'
	`$privateGame = '$privateGame'
	`$argString = '$argString'
	`$path = '$path'
	`$arguments = @('$([string]::Join("', '", $arguments))')
	Write-Output "arguments $([string]::Join(', ', $arguments))"
	`$cleanName = '$name'.Replace('[', '').Replace(']', '')
	if (-not `$$($nolog.ToString()))
	{
		Start-Transcript -path `"H:\GeneralsLogs\`$cleanName-$game-$df$privateGame.txt`"
	}
    try {
        #Write-Verbose `"C:\Python36-32\python.exe $path -name $name -g $game $argString`" -verbose
        C:\Python36-32\python.exe "$path" -name '$name' -g '$game' @arguments 2>&1 
    } 
    catch 
    {
        Write-Error `$_
    }
    finally 
    {	
		if (-not `$$($nolog.ToString()))
		{
			stop-transcript
		}
    }
    PING 127.0.0.1 -n 1 | out-null
	Get-ChildItem "H:\GeneralsLogs" -Recurse | ? { `$_.LastWriteTime -lt (get-date).AddMinutes(-30) } | Remove-Item -Force -Recurse -ErrorAction Ignore
"@

	Write-Verbose $exeString -Verbose
	start Powershell $exeString -Wait -NoNewWindow
	Write-Verbose 'Powershell finished, sleeping' -Verbose
}



function Run-SoraAI {
    Param(
        $name, 
        [string[]]
        $game, 
        [switch]$public, 
        [switch]$right, 
        $privateGame, 
        [switch]$noui
    )

}


function run-bot { 
    Param(
        $name, 
        [string[]]
        $game, 
        [switch]$public, 
        [switch]$right, 
        $privateGame, 
        [switch]$noui,
		$path = "C:\generals-bot\bot_ek0x45.py",
		[switch]$nolog
    )
    $games = $game
    while($true)
    {
        foreach ($g in $games)
        {
            write-verbose $g -verbose
            $psboundparameters['game'] = $g
            run-botonce @psboundparameters
        }     
    }
}


function run-botcheckpoint { 
    Param(
        $name, 
        [string[]]
        $game, 
        [switch]$public, 
        [switch]$right, 
        $privateGame, 
        [switch]$noui,
        [switch]$nocopy,
		[switch]$nolog
    )
    $games = $game
    if (-not $nocopy)
    {
		$date = Get-Date -Format 'yyyy-MM-dd'
		create-checkpoint -backup "C:\generals-bot-historical\generals-bot-$date"
    }
    while($true)
    {
        foreach ($g in $games)
        {
            write-verbose $g -verbose
            $psboundparameters['game'] = $g
            run-botonce @psboundparameters -path "C:\generals-bot-checkpoint\bot_ek0x45.py"
        }
    }
}


function create-checkpoint {
	Param(
		$source = 'C:\generals-bot\',
		$dest = 'C:\generals-bot-checkpoint\',
		$backup = $null
	)
	if ($backup)
	{
		robocopy $source $backup /MIR
	}
	robocopy $source $dest /MIR
}