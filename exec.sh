# !/bin/sh
 #BUILD_CC="x86_64-linux-gnu-gcc" \
 CC="mips64el-unknown-linux-gnu-gcc -mabi=32 " \
 AR="mips64el-unknown-linux-gnu-ar" AS="mips64el-unknown-linux-gnu-as" \
 LD="mips64el-unknown-linux-gnu-ld" NM="mips64el-unknown-linux-gnu-nm" \
 OBJCOPY="mips64el-unknown-linux-gnu-objcopy" \
 OBJDUMP="mips64el-unknown-linux-gnu-objdump" \
 RANLIB="mips64el-unknown-linux-gnu-ranlib" \
 CXX="mips64el-unknown-linux-gnu-g++" \
 CPP="mips64el-unknown-linux-gnu-cpp" \
 BUILD_CC="gcc" \
 HOST_CFLAGS="-I/usr/include" \
 HOST_CXXFLAGS="-I/usr/include" \
 HOST_CC="gcc" \
 BUILD_CC="gcc" \
 HOST_CXX="g++" \
 LDFLAGS="-L/opt/loongson3a-cross/tools/mips64el-unknown-linux-gnu/lib \
 -L/opt/loongson3a-cross/redhat/lib \
 -L/opt/loongson3a-cross/redhat/usr/lib" \
 CXXFLAGS="-I/opt/loongson3a-cross/redhat/usr/include \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-2.0/gdk \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-2.0/gdk-pixbuf \
 -I/opt/loongson3a-cross/redhat/usr/include/atk-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/cairo \
 -I/opt/loongson3a-cross/redhat/usr/include/pango-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/gio-unix-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/gio-unix-2.0/gio \
 -I/opt/loongson3a-cross/redhat/usr/include/glib-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/pixman-1 \
 -I/opt/loongson3a-cross/redhat/usr/include/freetype2 \
 -I/opt/loongson3a-cross/redhat/usr/include/libpng12 \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-unix-print-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/dbus-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/lib/qt-3.3/include" \
 CFLAGS="-I/opt/loongson3a-cross/redhat/usr/include \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-2.0/gdk \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/pango-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-2.0/gdk-pixbuf \
 -I/opt/loongson3a-cross/redhat/usr/include/cairo \
 -I/opt/loongson3a-cross/redhat/usr/include/gio-unix-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/gio-unix-2.0/gio \
 -I/opt/loongson3a-cross/redhat/usr/include/glib-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/pixman-1 \
 -I/opt/loongson3a-cross/redhat/usr/include/freetype2 \
 -I/opt/loongson3a-cross/redhat/usr/include/libpng12 \
 -I/opt/loongson3a-cross/redhat/usr/include/gtk-unix-print-2.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/atk-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/pango-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/include/dbus-1.0 \
 -I/opt/loongson3a-cross/redhat/usr/lib/qt-3.3/include" \
 ../mozilla-esr24/configure \
 --build=x86_64-linux-gnu --host=x86_64-linux-gnu --target=mips64el-unknown-linux-gnu \
 --prefix=/home/huangwenjun/firefox-new --disable-gstreamer \
 --with-arch=mips3 \
 --with-system-root=/opt/loongson3a-cross/redhat \
 --enable-application=browser \
 --disable-webrtc \
 --disable-tests \
 --with-pthreads \
 --disable-updater \
 --enable-optimize=-O3 \
 --disable-debug
 #--enable-tee
 #--without-system-nspr
 #--with-system-nss --with-nss-prefix=/opt/loongson3a-cross/tools/mips64el-unknown-linux-gnu
 #--with-system-nss --with-nss-prefix=/usr/lib/x86_64-linux-gnu

 #--enable-default-toolkit=cairo-gtk2
 #CXX="mips64el-unknown-linux-gnu-g++" \
 #HOST_CC="gcc" \
 #CPP="mips64el-unknown-linux-gnu-cpp"
 #--build=x86_64-linux-gnu --host=mips64el-unknown-linux-gnu --prefix=/home/huangwenjun/firefox
 #CPP="mips64el-unknown-linux-gnu-cpp"  ./configure \
 #--build=x86_64-linux-gnu --host=mips64el-unknown-linux-gnu --prefix=/home/huangwenjun/firefox

