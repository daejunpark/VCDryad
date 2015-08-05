@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN AFWP ======================
%r% %test_dir%\afwp\SLL-create.c ^
    %test_dir%\afwp\SLL-delete-all.c ^
    %test_dir%\afwp\SLL-delete.c ^
    %test_dir%\afwp\SLL-filter.c ^
    %test_dir%\afwp\SLL-find.c ^
    %test_dir%\afwp\SLL-insert.c ^
    %test_dir%\afwp\SLL-last.c ^
    %test_dir%\afwp\SLL-merge.c ^
    %test_dir%\afwp\SLL-reverse.c ^
    %test_dir%\afwp\SLL-rotate.c ^
    %test_dir%\afwp\SLL-swap.c ^
    %test_dir%\afwp\DLL-fix.c ^
    %test_dir%\afwp\DLL-splice.c ^
    | findstr "Verification function error"
echo ======================  END AFWP ======================
