; ============================================================
; Instalador de EasyPresenter para Windows
; Inno Setup 6
; ============================================================

#define MyAppName "EasyPresenter"
#define MyAppVersion "1.4.6"
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

UninstallDisplayIcon={app}\{#MyAppExeName}

; Si tienes el icono .ico puedes activar esto:
; SetupIconFile=assets\icon.ico


[Languages]

Name: "spanish"; MessagesFile: "compiler:Languages\Spanish.isl"


[Tasks]
Name: "desktopicon"; Description: "Crear un acceso directo en el escritorio"

[Files]

; ============================================================
; EJECUTABLE
; ============================================================

Source: "{#BuildDir}\{#MyAppExeName}";
DestDir: "{app}";
Flags: ignoreversion


; ============================================================
; DLLs
;
; El workflow copia aquí:
; - pdfium.dll
; - DLLs de GStreamer
; - DLLs de GLib
; - DLLs de dependencias
; ============================================================

Source: "{#BuildDir}\*.dll";
DestDir: "{app}";
Flags: ignoreversion


; ============================================================
; GSTREAMER PLUGINS
;
; El workflow crea:
;
; release\
;   lib\
;     gstreamer-1.0\
;
; ============================================================

Source: "{#BuildDir}\lib\gstreamer-1.0\*";
DestDir: "{app}\lib\gstreamer-1.0";
Flags: ignoreversion recursesubdirs createallsubdirs


; ============================================================
; DATOS
; ============================================================

Source: "data\*";
DestDir: "{app}\data";
Flags: ignoreversion recursesubdirs createallsubdirs skipifsourcedoesntexist


; ============================================================
; ASSETS
; ============================================================

Source: "assets\*";
DestDir: "{app}\assets";
Flags: ignoreversion recursesubdirs createallsubdirs skipifsourcedoesntexist


[Icons]

Name: "{group}\{#MyAppName}";
Filename: "{app}\{#MyAppExeName}"

Name: "{group}\Desinstalar {#MyAppName}";
Filename: "{uninstallexe}"

Name: "{autodesktop}\{#MyAppName}";
Filename: "{app}\{#MyAppExeName}";
Tasks: desktopicon


[Registry]

; ============================================================
; GSTREAMER
;
; Indica a GStreamer dónde están los plugins instalados.
; ============================================================

Root: HKCU;
Subkey: "Environment";
ValueType: expandsz;
ValueName: "GST_PLUGIN_PATH";
ValueData: "{app}\lib\gstreamer-1.0";
Flags: preservestringtype


[Run]

Filename: "{app}\{#MyAppExeName}";
Description: "Ejecutar {#MyAppName}";
Flags: nowait postinstall skipifsilent