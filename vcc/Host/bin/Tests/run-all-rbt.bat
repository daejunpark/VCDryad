@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN RBT ======================
%r% %test_dir%\rbt\rbt-find-smallest.c ^
    %test_dir%\rbt\rbt-insert-left-fixup.c ^
    %test_dir%\rbt\rbt-insert-right-fixup.c ^
    | findstr "Verification function error"
echo ======================  END RBT ======================
