@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN SL ======================
%r% %test_dir%\grass\sl_concat.c ^
    %test_dir%\grass\sl_copy.c ^
    %test_dir%\grass\sl_dispose.c ^
    %test_dir%\grass\sl_filter.c ^
    %test_dir%\grass\sl_insert.c ^
    %test_dir%\grass\sl_remove.c ^
    %test_dir%\grass\sl_reverse.c ^
    %test_dir%\grass\sl_traverse.c ^
    | findstr "Verification function error"
echo ======================  END SL ======================
