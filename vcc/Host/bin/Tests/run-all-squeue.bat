@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN SQUEUE ======================
%r% %test_dir%\bsd-squeue\bsd_squeue_init.c ^
    %test_dir%\bsd-squeue\bsd_squeue_insert_head.c ^
    %test_dir%\bsd-squeue\bsd_squeue_insert_tail.c ^
    %test_dir%\bsd-squeue\bsd_squeue_remove_head.c ^
    | findstr "simpleq verification error"
echo ======================  END SQUEUE ======================
