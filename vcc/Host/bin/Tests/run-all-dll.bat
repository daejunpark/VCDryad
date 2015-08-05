@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN DLL ======================
%r% %test_dir%\dll\dll-insert-front.c ^
    %test_dir%\dll\dll-insert-back.c ^
    %test_dir%\dll\dll-append.c ^
    %test_dir%\dll\dll-delete-all.c ^
    %test_dir%\dll\dll-mid-delete.c ^
    %test_dir%\dll\dll-meld.c ^
    %test_dir%\dll\dll-mid-insert.c ^
    | findstr "dll_insert dll_append dll_delete dll_mid dll_meld function error"
echo ======================  END DLL ======================
