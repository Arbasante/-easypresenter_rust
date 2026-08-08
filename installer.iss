; ============================================================
;  Instalador de EasyPresenter para Windows (Inno Setup)
; ============================================================

#define MyAppName "EasyPresenter"
#define MyAppVersion "1.0.0"
#define MyAppPublisher "Arbasante"
#define MyAppExeName "easy-presenter-slint.exe"
#define BuildDir "target\x86_64-pc-windows-msvc\release"

[Setup]
AppId={{B4B6A5B0-6E2F-4F2C-9A9D-EASYPRESENTER1}}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={autopf}\{#MyAppName}
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
OutputDir=Output
OutputBaseFilename=EasyPresenter-Setup-{#MyAppVersion}
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
ArchitecturesAllowed=x64
ArchitecturesInstallIn64BitMode=x64
; Descomenta si tienes un icono .ico en assets:
; SetupIconFile=assets\icon.ico
UninstallDisplayIcon={app}\{#MyAppExeName}

[Languages]
Name: "spanish"; MessagesFile: "compiler:Languages\Spanish.isl"

[Tasks]
Name: "desktopicon"; Description: "Crear un acceso directo en el escritorio"; GroupDescription: "Accesos directos:"

[Files]
; Ejecutable principal
Source: "{#BuildDir}\{#MyAppExeName}"; DestDir: "{app}"; Flags: ignoreversion

; Librerías necesarias (pdfium, gstreamer core dlls) copiadas junto al exe por el workflow
Source: "{#BuildDir}\*.dll"; DestDir: "{app}"; Flags: ignoreversion skipifsourcedoesntexist recursesubdirs

; Plugins de GStreamer
Source: "{#BuildDir}\gstreamer-1.0\*"; DestDir: "{app}\gstreamer-1.0"; Flags: ignoreversion recursesubdirs createallsubdirs skipifsourcedoesntexist

; Datos de la app (base de datos, etc.)
Source: "data\*"; DestDir: "{app}\data"; Flags: ignoreversion recursesubdirs createallsubdirs skipifsourcedoesntexist

; Assets (íconos, recursos)
Source: "assets\*"; DestDir: "{app}\assets"; Flags: ignoreversion recursesubdirs createallsubdirs skipifsourcedoesntexist

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{group}\Desinstalar {#MyAppName}"; Filename: "{uninstallexe}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Registry]
; Variable de entorno para que GStreamer encuentre los plugins portables
Root: HKCU; Subkey: "Environment"; ValueType: expandsz; ValueName: "GST_PLUGIN_PATH"; ValueData: "{app}\gstreamer-1.0"; Flags: preservestringtype

[Run]
Filename: "{app}\{#MyAppExeName}"; Description: "Ejecutar {#MyAppName}"; Flags: nowait postinstall skipifsilent
