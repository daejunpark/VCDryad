@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN BST ======================
%r% %test_dir%\bst\bst-insert-rec.c ^
    %test_dir%\bst\bst-find-rec.c ^
    %test_dir%\bst\bst-find-iter.c ^
    %test_dir%\bst\bst-delete-rec.c ^
    %test_dir%\bst\bst-remove-root-rec.c ^
    | findstr "Verification function error"
echo ======================  END BST ======================
