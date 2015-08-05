@echo off
set test_dir="..\Tests"
set run="..\Debug\vcc"
echo ====================== BEGIN SLL ======================
%run% %test_dir%\sll\sll-insert.c ^
      %test_dir%\sll\sll-delete-all.c ^
      %test_dir%\sll\sll-reverse.c ^
      %test_dir%\sll\sll-find.c ^
      %test_dir%\sll\sll-insert-front.c ^
      %test_dir%\sll\sll-insert-back.c ^
      %test_dir%\sll\sll-copy-all.c ^
      %test_dir%\sll\sll-append.c ^
      | findstr "insert delete reverse sll_find front back copy append function error"
echo ======================  END SLL ======================
