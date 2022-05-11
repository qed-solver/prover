(use-modules (guix channels))

(cons* 
 (channel
   (name 'rroohhh)
   (url "https://github.com/rroohhh/guix_packages")
   (branch "master"))
 %default-channels)
