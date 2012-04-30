(defadvice byte-compile-warn (around shut-up-about-cl activate compile)
  (let* ((fmt (ad-get-arg 0)))
    (unless (string-match "cl package" fmt)
      ad-do-it)))
