@echo off
set r="..\Debug\vcc"
set test_dir="..\Tests"
echo ====================== BEGIN AVL ======================
%r% %test_dir%\avl\avl-find-smallest.c ^
    %test_dir%\avl\avl-insert-rec.c ^
    %test_dir%\avl\avl-delete-rec.c ^
    %test_dir%\avl\avl-balance.c ^
    | findstr "Verification function error"
echo ======================  END AVL ======================
