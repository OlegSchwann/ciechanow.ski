"use strict";

let animated_drawers = [];
let unit_drawers = [];
let global_location_drawers = [];
let planet_scale_drawers = [];
let textured_drawers = [];
let eph_drawers = [];

let drawers_map = {};

let metric;
let short_time = true;

let textures_ready = false;
let eph;

let global_lat = 37.293244 * Math.PI / 180;
let global_lon = -122.058491 * Math.PI / 180;

let queried_lat_lon = false;

let global_start_date = new Date();
let global_start_t = global_start_date.getTime() / 86400000 + 2440587.5;

let em4a_seg;

download_file("/models/moon_eph.dat", function (buffer) {
    eph = new Ephemeris(buffer);

    eph_drawers.forEach(drawer => drawer.request_repaint());
});

const elevation_lut = [
    [3, 5, 16, 255],
    [28, 17, 44, 255],
    [54, 24, 62, 255],
    [82, 30, 77, 255],
    [112, 31, 87, 255],
    [142, 30, 91, 255],
    [173, 23, 88, 255],
    [202, 26, 80, 255],
    [225, 50, 67, 255],
    [238, 84, 63, 255],
    [243, 119, 82, 255],
    [245, 150, 109, 255],
    [246, 180, 142, 255],
    [247, 208, 182, 255],
    [249, 236, 221, 255],
];


function Ephemeris(buffer) {

    const eph_start_date = 2458416.500000;
    const eph_end_date = 2497136.500000;
    const eph_emb_offset = 0;
    const eph_moon_offset = 43560;
    const eph_sun_offset = 217800;
    const eph_emb_coeffs = 6;
    const eph_moon_coeffs = 6;
    const eph_sun_coeffs = 2;
    const eph_emb_interval_length = 16;
    const eph_moon_interval_length = 4;
    const eph_sun_interval_length = 16;
    const eph_star_offset = 929280;
    const eph_star_count = 9052;

    const j2000 = 2451545.0;

    this.eph_start_date = eph_start_date;
    this.eph_end_date = eph_end_date;

    const arc_sec_deg_rad = 4.8481368110953599e-6;
    let data = new Float32Array(buffer);

    this.star_data = new Float32Array(buffer, eph_star_offset);
    this.star_count = eph_star_count;

    let c = new Array(14);
    let v = new Array(14);

    function chebyshev_pos(x, coeffs, offset, count) {

        c[0] = 1;
        c[1] = x;

        for (let i = 2; i < count; i++) {
            c[i] = 2 * x * c[i - 1] - c[i - 2];
        }

        let xyz = [0, 0, 0];
        for (let i = count - 1; i >= 0; i--) {
            xyz[0] += c[i] * coeffs[offset + i];
            xyz[1] += c[i] * coeffs[offset + i + count];
            xyz[2] += c[i] * coeffs[offset + i + count * 2];
        }

        return xyz;
    }

    function chebyshev_vel(x, coeffs, offset, count) {

        c[0] = 1;
        c[1] = x;

        for (let i = 2; i < count; i++) {
            c[i] = 2 * x * c[i - 1] - c[i - 2];
        }

        v[0] = 0;
        v[1] = 1;
        v[2] = 4 * x;

        for (let i = 3; i < count; i++) {
            v[i] = 2 * x * v[i - 1] + 2 * c[i - 1] - v[i - 2];
        }

        let xyz = [0, 0, 0];
        for (let i = count - 1; i >= 0; i--) {
            xyz[0] += v[i] * coeffs[offset + i];
            xyz[1] += v[i] * coeffs[offset + i + count];
            xyz[2] += v[i] * coeffs[offset + i + count * 2];
        }

        return xyz;
    }

    this.sun_pos = function (t) {
        if (!data)
            return [0, 0, 0];

        t -= eph_start_date;

        const interval = Math.floor(t / eph_sun_interval_length);
        t -= interval * eph_sun_interval_length;

        let offset = eph_sun_offset + eph_sun_coeffs * interval * 3;

        const x = (t / eph_sun_interval_length) * 2.0 - 1.0;

        return chebyshev_pos(x, data, offset, eph_sun_coeffs);
    }


    this.emb_pos = function (t) {
        if (!data)
            return [-5486393.42818594, 134554638.13823962, 58370124.0435338]

        let s = this.sun_pos(t);
        t -= eph_start_date;

        const interval = Math.floor(t / eph_emb_interval_length);
        t -= interval * eph_emb_interval_length;

        let offset = eph_emb_offset + eph_emb_coeffs * interval * 3;

        const x = (t / eph_emb_interval_length) * 2.0 - 1.0;

        let p = chebyshev_pos(x, data, offset, eph_emb_coeffs);;
        return vec_sub(p, s);
    }

    this.emb_vel = function (t) {
        if (!data)
            return [-5486393.42818594, 134554638.13823962, 58370124.0435338]

        t -= eph_start_date;

        const interval = Math.floor(t / eph_emb_interval_length);
        t -= interval * eph_emb_interval_length;

        let offset = eph_emb_coeffs * interval * 3;

        const x = (t / eph_emb_interval_length) * 2.0 - 1.0;

        let vel = chebyshev_vel(x, data, offset, eph_emb_coeffs);

        const sc = 2.0 / eph_emb_interval_length / 3600 / 24;

        vel[0] *= sc;
        vel[1] *= sc;
        vel[2] *= sc;

        return vel;
    }

    this.moon_earth_pos = function (t) {

        if (!data)
            return [-121010.52240225673, 313259.80467510223, 127016.02393007278];

        t -= eph_start_date;

        const interval = Math.floor(t / eph_moon_interval_length);
        t -= interval * eph_moon_interval_length;

        let offset = eph_moon_offset + eph_moon_coeffs * interval * 3;

        const x = (t / eph_moon_interval_length) * 2.0 - 1.0;

        return chebyshev_pos(x, data, offset, eph_moon_coeffs);
    }

    this.moon_earth_vel = function (t) {

        if (!data)
            return [-121010.52240225673, 313259.80467510223, 127016.02393007278];

        t -= eph_start_date;

        const interval = Math.floor(t / eph_moon_interval_length);
        t -= interval * eph_moon_interval_length;

        let offset = eph_moon_offset + eph_moon_coeffs * interval * 3;

        const x = (t / eph_moon_interval_length) * 2.0 - 1.0;

        let vel = chebyshev_vel(x, data, offset, eph_emb_coeffs);

        const sc = 2.0 / eph_moon_interval_length / 3600 / 24;

        vel[0] *= sc;
        vel[1] *= sc;
        vel[2] *= sc;

        return vel;
    }

    this.earth_axial_tilt = function (t) {
        t -= j2000;
        let tc = t / 36525.0;

        return arc_sec_deg_rad * ((-46.8150 + (-0.00059 + (0.001813) * tc) * tc) * tc);
    }

    this.earth_rot_mat = function (t) {

        t -= j2000;

        let rot_a = 0;
        rot_a += 2 * Math.PI * (0.7790572732640 + 1.00273781191135448 * t);

        let axial = rot_z_mat3(rot_a);

        let tc = t / 36525.0;

        let tas2r = tc * arc_sec_deg_rad;
        let w = 2306.2181;

        let zeta = (w + ((0.30188) + 0.017998 * tc) * tc) * tas2r;

        let z = (w + ((1.09468) + 0.018203 * tc) * tc) * tas2r;

        let theta = ((2004.3109) + ((-0.42665) - 0.041833 * tc) * tc) * tas2r;


        let prec = rot_z_mat3(-zeta);
        prec = mat3_mul(rot_y_mat3(theta), prec);
        prec = mat3_mul(rot_z_mat3(-z), prec);

        let obl_angle = arc_sec_deg_rad * ((-46.8150 + (-0.00059 + (0.001813) * tc) * tc) * tc);

        let obl = rot_x_mat3(obl_angle);

        return mat3_mul(prec, mat3_mul(obl, axial));
    }

    this.moon_rot_mat = function (t) {

        t -= j2000;

        let T = t / 36525;

        const dtr = Math.PI / 180.0;

        let E1 = dtr * (125.045 - 0.0529921 * t);
        let E2 = dtr * (250.089 - 0.1059842 * t);
        let E3 = dtr * (260.008 + 13.0120009 * t);
        let E4 = dtr * (176.625 + 13.3407154 * t);
        let E5 = dtr * (357.529 + 0.9856003 * t);
        let E6 = dtr * (311.589 + 26.4057084 * t);
        let E7 = dtr * (134.963 + 13.0649930 * t);
        let E8 = dtr * (276.617 + 0.3287146 * t);
        let E9 = dtr * (34.226 + 1.7484877 * t);
        let E10 = dtr * (15.134 - 0.1589763 * t);
        let E11 = dtr * (119.743 + 0.0036096 * t);
        let E12 = dtr * (239.961 + 0.1643573 * t);
        let E13 = dtr * (25.053 + 12.9590088 * t);

        let alpha_iau_deg = 269.9949 + 0.0031 * T
            - 3.8787 * Math.sin(E1) - 0.1204 * Math.sin(E2) + 0.0700 * Math.sin(E3)
            - 0.0172 * Math.sin(E4) + 0.0072 * Math.sin(E6) - 0.0052 * Math.sin(E10)
            + 0.0043 * Math.sin(E13);

        let delta_iau_deg = 66.5392 + 0.0130 * T
            + 1.5419 * Math.cos(E1) + 0.0239 * Math.cos(E2) - 0.0278 * Math.cos(E3)
            + 0.0068 * Math.cos(E4) - 0.0029 * Math.cos(E6) + 0.0009 * Math.cos(E7)
            + 0.0008 * Math.cos(E10) - 0.0009 * Math.cos(E13);

        const Wdot = 13.17635815;

        let W = 38.3213 + Wdot * t - 1.4E-12 * t * t;
        + 3.5610 * Math.sin(E1) + 0.1208 * Math.sin(E2) - 0.0642 * Math.sin(E3)
            + 0.0158 * Math.sin(E4) + 0.0252 * Math.sin(E5) - 0.0066 * Math.sin(E6)
            - 0.0047 * Math.sin(E7) - 0.0046 * Math.sin(E8) + 0.0028 * Math.sin(E9)
            + 0.0052 * Math.sin(E10) + 0.0040 * Math.sin(E11) + 0.0019 * Math.sin(E12)
            - 0.0044 * Math.sin(E13);


        /* Map from GL right x, to front x */
        W += 90;

        let axial = rot_z_mat3(W * dtr);

        let mat = rot_y_mat3((90 - delta_iau_deg) * dtr)

        mat = mat3_mul(rot_z_mat3(alpha_iau_deg * dtr), mat);


        return mat3_mul(mat, axial);
    }
}

(function () {

    const pi = Math.PI;

    const sqrt = Math.sqrt;
    const sin = Math.sin;
    const cos = Math.cos;
    const acos = Math.acos;
    const asin = Math.asin;
    const atan2 = Math.atan2;
    const exp = Math.exp;
    const pow = Math.pow;
    const max = Math.max;
    const min = Math.min;
    const abs = Math.abs;
    const random = Math.random;
    const round = Math.round;
    const floor = Math.floor;
    const ceil = Math.ceil;

    const coarse_pointer = matchMedia("(pointer:coarse)").matches;

    const scale = (window.devicePixelRatio || 1);

    let all_drawers = [];
    let all_containers = [];

    let planet_scale = 0;

    const trail_history_count = 2048;

    const earth_radius = 6371;
    const earth_mass = 5.9724e24;

    const moon_radius = 1737.4;
    const moon_mass = 7.346e22;

    const sun_radius = 695700;

    const earth_moon_mass_ratio = 81.3005682214972154;

    const ecliptic_inclination = 0.4090928042;

    const G = 6.67430e-11;


    const color0 = "#EFC540";
    const color1 = "#EF7F39";
    const color2 = "#31C0B1";
    const color3 = "#256BB9";
    const color4 = "#DA7BA3";
    const color5 = "#A41247";

    const color_date = "#7290AF";
    const color_time = "#CDB57B";

    const color0h = 0xEFC540;
    const color1h = 0xEF7F39;
    const color2h = 0x31C0B1;
    const color3h = 0x256BB9;
    const color4h = 0xDA7BA3;
    const color5h = 0xA41247;

    const color_earth_h = 0x30557F;
    const color_moon_h = 0xB9B8B2;


    function toggle_planet_scale() {
        planet_scale = planet_scale == 0.0 ? 1.0 : 0.0;

        if (planet_scale > 0)
            document.body.classList.add("large_planets");
        else
            document.body.classList.remove("large_planets");

        planet_scale_drawers.forEach(drawer => drawer.request_repaint());
    }


    const gl = new GLDrawer(scale, function () {
        textures_ready = true;
        all_drawers.forEach(drawer => drawer.request_repaint());
    });

    const gl_mini = new GLDrawer(scale, function () { }, true);


    function GLDrawer(scale, ready_callback, mini) {

        const canvas = document.createElement("canvas");
        this.canvas = canvas;

        const gl = canvas.getContext('experimental-webgl', { antialias: true, stencil: true });
        gl.getExtension('OES_element_index_uint');
        gl.getExtension('OES_standard_derivatives');

        const lod_ext = gl.getExtension("EXT_shader_texture_lod");
        const float_ext = gl.getExtension("OES_texture_float");
        const half_float_ext = gl.getExtension("OES_texture_half_float");

        const float_linear_filtering = gl.getExtension("OES_texture_float_linear");
        const half_float_linear_filtering = gl.getExtension("OES_texture_half_float_linear");

        const linear_filtering = half_float_ext ? half_float_linear_filtering : float_linear_filtering;

        const draw_buffers = gl.getExtension("WEBGL_draw_buffers");

        let inst_ext = gl.getExtension('ANGLE_instanced_arrays');

        let assets = [
            { name: "moon_color" },
            { name: "moon_height_map", gl_type: gl.LUMINANCE },
            { name: "earth_color", mipmaps: true },
            { name: "earth_clouds", mipmaps: true, gl_type: gl.LUMINANCE },
            { name: "earth_sdf", gl_type: gl.LUMINANCE },
            { name: "noise", gl_type: gl.LUMINANCE }];

        if (mini) {
            assets = [{ name: "earth_sdf", gl_type: gl.LUMINANCE }];
        }
        let textures = {};
        let images = [];
        let loaded_image_count = 0;

        function image_loaded() {
            loaded_image_count++;

            if (loaded_image_count != assets.length)
                return;

            images.forEach((image, i) => {

                let asset = assets[i];
                let texture = gl.createTexture();

                gl.bindTexture(gl.TEXTURE_2D, texture);
                gl.pixelStorei(gl.UNPACK_COLORSPACE_CONVERSION_WEBGL, gl.NONE);

                let npot = (image.width & (image.width - 1)) != 0 || (image.height & (image.height - 1)) != 0
                gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, npot ? gl.CLAMP_TO_EDGE : gl.REPEAT);
                gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, npot ? gl.CLAMP_TO_EDGE : gl.REPEAT);
                gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
                gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);

                let gl_type = asset.gl_type || gl.RGBA;


                gl.texImage2D(gl.TEXTURE_2D, 0, gl_type, gl_type, gl.UNSIGNED_BYTE, image);

                if (asset.mipmaps && lod_ext) {
                    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
                    gl.generateMipmap(gl.TEXTURE_2D);
                }

                textures[asset.name] = texture;
            })

            ready_callback();
        }

        assets.forEach((asset, i) => {
            let image = new Image();
            images[i] = image;
            image.onload = image_loaded;
            image.src = "/images/moon/" + asset.name + ".png";
        });

        let elevation_lut_texture = gl.createTexture();

        gl.bindTexture(gl.TEXTURE_2D, elevation_lut_texture);

        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
        gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
        let pixels = new Uint8Array(flatten(elevation_lut));

        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, elevation_lut.length, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, pixels);

        gl.bindTexture(gl.TEXTURE_2D, null);


        const float_size = 4;

        let star_buffer = gl.createBuffer();
        gl.bindBuffer(gl.ARRAY_BUFFER, star_buffer);
        let copied_star_data = false;

        let history_trail_buffer = gl.createBuffer();
        gl.bindBuffer(gl.ARRAY_BUFFER, history_trail_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, trail_history_count * 3 * 4 * float_size, gl.DYNAMIC_DRAW);

        let blob_buffer = gl.createBuffer();
        gl.bindBuffer(gl.ARRAY_BUFFER, blob_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, 2048 * 2 * float_size, gl.DYNAMIC_DRAW);


        function make_mesh(w, h) {
            let vert = new Float32Array(w * h * 2);

            for (let i = 0; i < w; i++) {
                let x = (i / (w - 1) * 2 - 1);

                for (let k = 0; k < h; k++) {
                    let y = (k / (h - 1) * 2 - 1);

                    vert[(i * h + k) * 2] = x;
                    vert[(i * h + k) * 2 + 1] = y;
                }
            }

            let ind = new Int16Array((w - 1) * (h - 1) * 3 * 2);

            let t = 0;
            for (let i = 0; i < w - 1; i++) {

                let i0 = (i) * h;
                let i1 = (i + 1) * h;

                for (let k = 0; k < h - 1; k++) {

                    let k0 = k;
                    let k1 = k + 1;

                    ind[t++] = i0 + k0;
                    ind[t++] = i1 + k0;
                    ind[t++] = i0 + k1;

                    ind[t++] = i1 + k0;
                    ind[t++] = i1 + k1;
                    ind[t++] = i0 + k1;
                }
            }

            return [vert, ind];
        }

        let mesh_size = 200;
        let mesh_buffer = gl.createBuffer();
        let mesh_index_buffer = gl.createBuffer();


        if (!mini) {

            let b = make_mesh(mesh_size, mesh_size);

            gl.bindBuffer(gl.ARRAY_BUFFER, mesh_buffer);
            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, mesh_index_buffer);

            gl.bufferData(gl.ARRAY_BUFFER, b[0], gl.STATIC_DRAW);
            gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, b[1], gl.STATIC_DRAW);
        }


        const max_instance_count = 1 << 15;

        let instance_id_buffer = gl.createBuffer();

        let instance_ids = new Float32Array(max_instance_count);
        for (let i = 0; i < max_instance_count; i++)
            instance_ids[i] = i;

        gl.bindBuffer(gl.ARRAY_BUFFER, instance_id_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, instance_ids, gl.STATIC_DRAW);


        let binning_directions_buffer = gl.createBuffer();

        {
            let directions = new Float32Array([
                0, 0, 0,
                1, 0, 0,
                0, 1, 0,
                1, 1, 0,

                0, 0, 1,
                1, 0, 1,
                0, 1, 1,
                1, 1, 1,
            ]);

            gl.bindBuffer(gl.ARRAY_BUFFER, binning_directions_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, directions, gl.STATIC_DRAW);
        }

        let full_screen_vertices = [
            -1.0, -1.0,
            3.0, -1.0,
            -1.0, 3.0,
        ];

        let full_screen_vertex_buffer = gl.createBuffer();

        gl.bindBuffer(gl.ARRAY_BUFFER, full_screen_vertex_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(full_screen_vertices), gl.STATIC_DRAW);


        let line_vertex_buffer = gl.createBuffer();

        let line_vertices = [
            0.0, 1.0,
        ];

        gl.bindBuffer(gl.ARRAY_BUFFER, line_vertex_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(line_vertices), gl.STATIC_DRAW);


        let hexagon_vertex_buffer = gl.createBuffer();

        let hexagon_vertices = [
            1, 0,
            cos(pi * 120 / 180), sin(pi * 120 / 180),
            cos(pi * 240 / 180), sin(pi * 240 / 180),

            1, 0,
            cos(pi * 60 / 180), sin(pi * 60 / 180),
            cos(pi * 120 / 180), sin(pi * 120 / 180),

            cos(pi * 120 / 180), sin(pi * 120 / 180),
            cos(pi * 180 / 180), sin(pi * 180 / 180),
            cos(pi * 240 / 180), sin(pi * 240 / 180),

            cos(pi * 240 / 180), sin(pi * 240 / 180),
            cos(pi * 300 / 180), sin(pi * 300 / 180),
            1, 0,
        ];

        gl.bindBuffer(gl.ARRAY_BUFFER, hexagon_vertex_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(hexagon_vertices), gl.STATIC_DRAW);


        let quad_vertices = [
            -1.0, -1.0,
            1.0, -1.0,
            -1.0, 1.0,
            1.0, 1.0,
        ];


        let quad_vertex_buffer = gl.createBuffer();

        gl.bindBuffer(gl.ARRAY_BUFFER, quad_vertex_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(quad_vertices), gl.STATIC_DRAW);
        gl.bindBuffer(gl.ARRAY_BUFFER, null);


        let sphere_side_count = 20;
        let sphere_vertex_buffer = gl.createBuffer();
        let sphere_vertex_count = 6 * 6 * sphere_side_count * sphere_side_count;

        gl.bindBuffer(gl.ARRAY_BUFFER, sphere_vertex_buffer);

        let sphere = new Float32Array(sphere_vertex_count * 3);
        let sphere_i = 0;

        for (let side = 0; side < 6; side++) {

            let x_vec = [[1, 0, 0], [0, 1, 0], [-1, 0, 0], [0, -1, 0], [1, 0, 0], [-1, 0, 0]];
            let y_vec = [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, -1, 0], [0, -1, 0]];


            let norm = vec_cross(x_vec[side], y_vec[side]);

            for (let ix = 0; ix < sphere_side_count; ix++) {
                for (let iy = 0; iy < sphere_side_count; iy++) {

                    let s = [
                        (ix / sphere_side_count) * 2 - 1.0,
                        ((ix + 1) / sphere_side_count) * 2 - 1.0
                    ];

                    let t = [
                        (iy / sphere_side_count) * 2 - 1.0,
                        ((iy + 1) / sphere_side_count) * 2 - 1.0
                    ];

                    let x = [[], []];
                    let y = [[], []];
                    let z = [[], []];
                    let l = [[], []];

                    for (let i = 0; i < 2; i++) {
                        for (let k = 0; k < 2; k++) {
                            x[i][k] = s[k] * x_vec[side][0] + t[i] * y_vec[side][0] + norm[0];
                            y[i][k] = s[k] * x_vec[side][1] + t[i] * y_vec[side][1] + norm[1];
                            z[i][k] = s[k] * x_vec[side][2] + t[i] * y_vec[side][2] + norm[2];
                        }
                    }

                    for (let i = 0; i < 2; i++) {
                        for (let k = 0; k < 2; k++) {
                            l[i][k] = 1 / sqrt(x[i][k] * x[i][k] + y[i][k] * y[i][k] + z[i][k] * z[i][k]);
                        }
                    }

                    for (let pair of [[0, 0], [0, 1], [1, 0], [1, 0], [0, 1], [1, 1]]) {
                        sphere[sphere_i++] = x[pair[0]][pair[1]] * l[pair[0]][pair[1]];
                        sphere[sphere_i++] = y[pair[0]][pair[1]] * l[pair[0]][pair[1]];
                        sphere[sphere_i++] = z[pair[0]][pair[1]] * l[pair[0]][pair[1]];
                    }
                }
            }
        }

        gl.bufferData(gl.ARRAY_BUFFER, sphere, gl.STATIC_DRAW);


        let parted_sphere_vertex_buffer = gl.createBuffer();
        let parted_sphere_index_buffer = gl.createBuffer();
        let parted_sphere_index_count;
        {


            let n = 6;
            let nn = n * (n + 1) / 2;
            let vertex_count = 8 * nn;


            let sphere = new Float32Array(vertex_count * 3);
            let vert_i = 0;
            let ind_i = 0;
            let indices = [];



            for (let side = 0; side < 8; side++) {

                let a_vec = [(side & 1) ? 1 : -1, 0, 0];
                let b_vec = [0, (side & 2) ? 1 : -1, 0];
                let c_vec = [0, 0, (side & 4) ? 1 : -1];

                let shift = [a_vec[0], b_vec[1], c_vec[2]];

                let nv = n - 1;
                for (let iv = 0; iv <= nv; iv++) {

                    let nu = n - iv - 1;

                    for (let iu = 0; iu <= nu; iu++) {

                        let v = iv / nv;
                        let u = iu / (nu || 1);

                        let p = vec_lerp(vec_lerp(a_vec, c_vec, v),
                            vec_lerp(b_vec, c_vec, v), u);
                        p = vec_norm(p);
                        sphere[vert_i++] = p[0] + shift[0];
                        sphere[vert_i++] = p[1] + shift[1];
                        sphere[vert_i++] = p[2] + shift[2];
                    }
                }


                let v0 = nn * side;

                for (let iv = 0; iv < nv; iv++) {
                    indices[ind_i++] = v0 + iv;
                    indices[ind_i++] = v0 + iv + 1;
                    indices[ind_i++] = v0 + iv + n;
                }

                v0 += nv + 1;

                for (let iv = 1; iv < nv; iv++) {

                    let nu = n - iv - 1;

                    for (let iu = 0; iu < nu; iu++) {

                        indices[ind_i++] = v0 + iu;
                        indices[ind_i++] = v0 + iu + 1;
                        indices[ind_i++] = v0 + iu + nu + 1;

                        indices[ind_i++] = v0 + iu;
                        indices[ind_i++] = v0 + iu + 1;
                        indices[ind_i++] = v0 + iu - nu - 1;
                    }

                    v0 += nu + 1;
                }
            }


            for (let side = 0; side < 4; side++) {

                let v0 = side * nn;

                for (let iv = 0; iv < n - 1; iv++) {
                    indices[ind_i++] = v0 + iv;
                    indices[ind_i++] = v0 + iv + 1;
                    indices[ind_i++] = v0 + iv + nn * 4;

                    indices[ind_i++] = v0 + iv + 1;
                    indices[ind_i++] = v0 + iv + nn * 4;
                    indices[ind_i++] = v0 + iv + nn * 4 + 1;
                }
            }

            for (let side = 0; side < 4; side++) {

                let v0 = (side & 1) * nn + nn * 2 * (side & 2);
                let v1 = (side & 1) * nn * 2 + 2 * nn * (side & 2);

                let jump = nn * 2;
                let jump2 = nn;

                let k = n;
                for (let iv = 0; iv < n - 1; iv++) {
                    indices[ind_i++] = v0;
                    indices[ind_i++] = v0 + k;
                    indices[ind_i++] = v0 + jump;

                    indices[ind_i++] = v0 + k;
                    indices[ind_i++] = v0 + jump + k;
                    indices[ind_i++] = v0 + jump;

                    indices[ind_i++] = v1 + k - 1;
                    indices[ind_i++] = v1 + k + k - 2;
                    indices[ind_i++] = v1 + jump2 + k - 1;

                    indices[ind_i++] = v1 + k + k - 2;
                    indices[ind_i++] = v1 + jump2 + k + k - 2;
                    indices[ind_i++] = v1 + jump2 + k - 1;

                    v0 += k;
                    v1 += k;
                    k--;
                }
            }

            indices[ind_i++] = 0;
            indices[ind_i++] = nn * 2;
            indices[ind_i++] = nn * 6;
            indices[ind_i++] = 0;
            indices[ind_i++] = nn * 6;
            indices[ind_i++] = nn * 4;

            indices[ind_i++] = nn * 3;
            indices[ind_i++] = nn * 7;
            indices[ind_i++] = nn * 5;
            indices[ind_i++] = nn * 1;
            indices[ind_i++] = nn * 3;
            indices[ind_i++] = nn * 5;


            indices[ind_i++] = nn * 3 + nn - 1;
            indices[ind_i++] = nn * 1 + nn - 1;
            indices[ind_i++] = nn * 0 + nn - 1;
            indices[ind_i++] = nn * 3 + nn - 1;
            indices[ind_i++] = nn * 2 + nn - 1;
            indices[ind_i++] = nn * 0 + nn - 1;


            indices[ind_i++] = nn * 5 + nn - 1;
            indices[ind_i++] = nn * 6 + nn - 1;
            indices[ind_i++] = nn * 4 + nn - 1;
            indices[ind_i++] = nn * 5 + nn - 1;
            indices[ind_i++] = nn * 6 + nn - 1;
            indices[ind_i++] = nn * 7 + nn - 1;

            indices[ind_i++] = nn * 1 + n - 1;
            indices[ind_i++] = nn * 4 + n - 1;
            indices[ind_i++] = nn * 0 + n - 1;
            indices[ind_i++] = nn * 1 + n - 1;
            indices[ind_i++] = nn * 4 + n - 1;
            indices[ind_i++] = nn * 5 + n - 1;

            indices[ind_i++] = nn * 2 + n - 1;
            indices[ind_i++] = nn * 3 + n - 1;
            indices[ind_i++] = nn * 6 + n - 1;
            indices[ind_i++] = nn * 7 + n - 1;
            indices[ind_i++] = nn * 3 + n - 1;
            indices[ind_i++] = nn * 6 + n - 1;


            parted_sphere_index_count = ind_i;

            gl.bindBuffer(gl.ARRAY_BUFFER, parted_sphere_vertex_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, sphere, gl.STATIC_DRAW);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, parted_sphere_index_buffer);
            gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(indices), gl.STATIC_DRAW);
        }


        let curve_index_buffer = gl.createBuffer();
        let curve_vertex_buffer = gl.createBuffer();
        let curve_index_count;

        {
            let n = 192;
            let m = 12;

            let vertices = [];
            let indices = [];

            for (let j = 0; j <= n; j++) {
                for (let i = 0; i <= m; i++) {
                    vertices.push(j / n);
                    vertices.push(2 * pi * i / m);
                }
            }

            for (let i = 0; i < m; i++) {
                for (let j = 0; j < n; j++) {

                    indices.push(j * (m + 1) + i);
                    indices.push(j * (m + 1) + i + m + 2);
                    indices.push(j * (m + 1) + i + 1);

                    indices.push(j * (m + 1) + i);
                    indices.push(j * (m + 1) + i + m + 1);
                    indices.push(j * (m + 1) + i + m + 2);
                }
            }

            curve_index_count = indices.length;

            gl.bindBuffer(gl.ARRAY_BUFFER, curve_vertex_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(vertices), gl.STATIC_DRAW);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, curve_index_buffer);
            gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(indices), gl.STATIC_DRAW);
        }

        let cone_index_buffer = gl.createBuffer();
        let cone_vertex_buffer = gl.createBuffer();
        let cone_index_count;

        {
            let n = 192;

            let vertices = [];
            let indices = [];

            for (let j = 0; j <= n; j++) {

                let a = j / n * 2 * pi;

                vertices.push(cos(a));
                vertices.push(sin(a));
                vertices.push(1);

                vertices.push(cos(a));
                vertices.push(sin(a));
                vertices.push(0);
            }

            for (let j = 0; j < n * 2; j++) {

                indices.push(j);
                indices.push(j + 1);
                indices.push(j + 2);

            }

            cone_index_count = indices.length;

            gl.bindBuffer(gl.ARRAY_BUFFER, cone_vertex_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(vertices), gl.STATIC_DRAW);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, cone_index_buffer);
            gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(indices), gl.STATIC_DRAW);
        }


        let segment_index_buffer = gl.createBuffer();
        let segment_vertex_buffer = gl.createBuffer();
        let segment_index_count;

        {
            let n = 1;
            let m = 12;

            let vertices = [];
            let indices = [];

            for (let j = 0; j <= n; j++) {
                for (let i = 0; i <= m; i++) {
                    vertices.push(j / n);
                    vertices.push(2 * pi * i / m);
                }
            }

            for (let i = 0; i < m; i++) {
                for (let j = 0; j < n; j++) {

                    indices.push(j * (m + 1) + i);
                    indices.push(j * (m + 1) + i + m + 2);
                    indices.push(j * (m + 1) + i + 1);

                    indices.push(j * (m + 1) + i);
                    indices.push(j * (m + 1) + i + m + 1);
                    indices.push(j * (m + 1) + i + m + 2);
                }
            }

            segment_index_count = indices.length;

            gl.bindBuffer(gl.ARRAY_BUFFER, segment_vertex_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(vertices), gl.STATIC_DRAW);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, segment_index_buffer);
            gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(indices), gl.STATIC_DRAW);
        }


        let arrow_index_buffer = gl.createBuffer();
        let arrow_vertex_buffer = gl.createBuffer();
        let arrow_index_count;

        {
            // arrow
            let n = 40;
            let m = 9;


            let vertices = [];
            let indices = [];

            for (let j = 0; j <= n; j++) {

                let t = j / n;

                let x = Math.cos(t * Math.PI * 2);
                let y = Math.sin(t * Math.PI * 2);

                for (let i = 0; i <= m; i++) {

                    let r = 0.9;
                    let nz = 0;
                    let nx = x;
                    let ny = y;
                    let z = -12;
                    let s = 1;

                    if (i == 0) {
                        r = 0;
                        nz = -1;
                        nx = ny = 0;
                    } else if (i == 1) {
                        nz = -1;
                        nx = ny = 0;
                    } else if (i == 2) {

                    } else if (i == 3) {
                        z = -9;
                    } else if (i == 4) {
                        s = 0.6;
                        z = -6;
                    } else if (i == 5) {
                        z = -6;
                        s = 0.6;
                        nz = -1;
                        nx = ny = 0;
                    } else if (i == 6) {
                        r = 2.5;
                        z = -6.;
                        nz = -1;
                        nx = ny = 0;
                    }
                    else if (i == 7) {
                        r = 2.5;
                        z = -6;
                        nz = 0.5;
                    }
                    else if (i == 8) {
                        r = 0.1;
                        z = -0.2;
                        nz = 0.5;
                    } else if (i == 9) {
                        r = 0;
                        z = 0;
                        nz = 0.3;
                    }


                    vertices.push(x * r);
                    vertices.push(y * r);
                    vertices.push(z);

                    let v = [nx, ny, nz];
                    v = vec_norm(v);

                    vertices.push(v[0]);
                    vertices.push(v[1]);
                    vertices.push(v[2]);
                    vertices.push(s);
                }
            }

            for (let i = 0; i < m; i++) {
                for (let j = 0; j < n; j++) {

                    indices.push(+ j * (m + 1) + i);
                    indices.push(j * (m + 1) + i + m + 2);
                    indices.push(j * (m + 1) + i + 1);


                    indices.push(j * (m + 1) + i);
                    indices.push(j * (m + 1) + i + m + 1);
                    indices.push(j * (m + 1) + i + m + 2);
                }
            }

            arrow_index_count = indices.length;

            gl.bindBuffer(gl.ARRAY_BUFFER, arrow_vertex_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(vertices), gl.STATIC_DRAW);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, arrow_index_buffer);
            gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, new Uint32Array(indices), gl.STATIC_DRAW);
        }






        let tetra_weights = [
            1, 0, 0, 0, 1, 0, 0, 0,
            0, 1, 0, 0, 1, 0, 0, 0,
            0, 0, 0, 1, 1, 0, 0, 0,

            1, 0, 0, 0, 0, 1, 0, 0,
            0, 0, 1, 0, 0, 1, 0, 0,
            0, 1, 0, 0, 0, 1, 0, 0,

            1, 0, 0, 0, 0, 0, 1, 0,
            0, 0, 0, 1, 0, 0, 1, 0,
            0, 0, 1, 0, 0, 0, 1, 0,

            0, 1, 0, 0, 0, 0, 0, 1,
            0, 0, 1, 0, 0, 0, 0, 1,
            0, 0, 0, 1, 0, 0, 0, 1,
        ];


        let tetra_weights_buffer = gl.createBuffer();

        gl.bindBuffer(gl.ARRAY_BUFFER, tetra_weights_buffer);
        gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(tetra_weights), gl.STATIC_DRAW);
        gl.bindBuffer(gl.ARRAY_BUFFER, null);



        let tetra_prism_weights_buffer = gl.createBuffer();
        let tetrahedron_instance_vertex_buffer = gl.createBuffer();
        let tetra_inst_count;

        {
            let tetra_pirsm_weights = [
                1, 0, 0, 0, -1, 0, 0, 0,
                0, 1, 0, 0, 0, -1, 0, 0,
                0, 0, 1, 0, 0, 0, -1, 0,
                0, 0, 0, 1, 0, 0, 0, -1,
                1, 0, 0, 0, -1, 0, 0, 0,
            ];

            gl.bindBuffer(gl.ARRAY_BUFFER, tetra_prism_weights_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(tetra_pirsm_weights), gl.STATIC_DRAW);
            gl.bindBuffer(gl.ARRAY_BUFFER, null);

            let tetra_ns = 48 * 48;
            let tetra_nz = 20;
            tetra_inst_count = tetra_nz * tetra_ns;
            let tetra_inst_vertices = new Float32Array(tetra_inst_count * 4 * 3);

            let i = 0;
            for (let z = 0; z < tetra_nz; z++) {
                for (let y = 0; y < tetra_ns; y++) {

                    const i0 = hash(450.1352 * i + 231.04);
                    const i1 = hash(7642.5645 * i + 345.5);
                    const i2 = hash(1642.315 * i + 942.1);

                    const a = 2.39996323;


                    let pr = 0.6 * sqrt(y);
                    let theta = a * y + z;

                    let xx = cos(theta) * pr + (i0 - 0.5) * 1;
                    let yy = sin(theta) * pr + (i1 - 0.5) * 1;
                    let zz = -z * 0.15 + i2 * 0.15;

                    let mat = rot_x_mat3(i0 * pi * 2);
                    mat = mat3_mul(rot_y_mat3(i1 * pi * 2), mat);
                    mat = mat3_mul(scale_mat3(i2 * 0.25 + 0.15), mat);

                    let p0 = mat3_mul_vec(mat, [1, -1, -1]);
                    let p1 = mat3_mul_vec(mat, [1, 1, 1]);
                    let p2 = mat3_mul_vec(mat, [-1, 1, -1]);
                    let p3 = mat3_mul_vec(mat, [-1, -1, 1]);


                    tetra_inst_vertices[i * 12 + 0 + 0] = p0[0] + xx;
                    tetra_inst_vertices[i * 12 + 0 + 1] = p0[1] + yy;
                    tetra_inst_vertices[i * 12 + 0 + 2] = p0[2] + zz;

                    tetra_inst_vertices[i * 12 + 3 + 0] = p1[0] + xx;
                    tetra_inst_vertices[i * 12 + 3 + 1] = p1[1] + yy;
                    tetra_inst_vertices[i * 12 + 3 + 2] = p1[2] + zz;

                    tetra_inst_vertices[i * 12 + 6 + 0] = p2[0] + xx;
                    tetra_inst_vertices[i * 12 + 6 + 1] = p2[1] + yy;
                    tetra_inst_vertices[i * 12 + 6 + 2] = p2[2] + zz;

                    tetra_inst_vertices[i * 12 + 9 + 0] = p3[0] + xx;
                    tetra_inst_vertices[i * 12 + 9 + 1] = p3[1] + yy;
                    tetra_inst_vertices[i * 12 + 9 + 2] = p3[2] + zz;

                    i++
                }
            }


            gl.bindBuffer(gl.ARRAY_BUFFER, tetrahedron_instance_vertex_buffer);
            gl.bufferData(gl.ARRAY_BUFFER, tetra_inst_vertices, gl.STATIC_DRAW);
            gl.bindBuffer(gl.ARRAY_BUFFER, null);

        }


        let srgb_tex_preamble =
            `
        mediump vec3 convert_color(mediump vec3 c) {
            c.r = c.r < 0.04045 ? c.r * (1.0/12.92) : pow((c.r + 0.055)/1.055, 2.4);
            c.g = c.g < 0.04045 ? c.g * (1.0/12.92) : pow((c.g + 0.055)/1.055, 2.4);
            c.b = c.b < 0.04045 ? c.b * (1.0/12.92) : pow((c.b + 0.055)/1.055, 2.4);
            return c;
        }
        `


        let srgb_frag_src =
            `
        lowp float linear_to_srgb(lowp float c) {
            return c < 0.0031308 ? 12.92 * c : 1.055 * pow(c, 1.0/2.4) - 0.055;
        }
        `

        let preamble_src =
            `
            #extension GL_OES_standard_derivatives : enable

            precision highp float;

            uniform sampler2D u_tex_noise;

            uniform vec3 u_camera_pos;
            uniform vec3 u_screen_pos;
            uniform vec3 u_screen_up;
            uniform vec3 u_screen_right;
            uniform vec3 u_light_dir;

            float PI = 3.141592741;
            float RAY_MAX = 1.0e10;

            float linear_to_srgb(float c) {
                return c < 0.0031308 ? 12.92 * c : 1.055 * pow(c, 1.0/2.4) - 0.055;
            }

            float noise(float c) {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return c + n * (1.5/255.0) - 0.75/255.0;
            }

            float quick_sphere(vec3 ray_org, vec3 ray_dir, vec3 pos, float r2) {
                vec3 oc = ray_org - pos;
                float b = dot(oc, ray_dir);
                float c = dot(oc, oc) - r2;
                float h = b*b - c;
                
                if (h<0.0) return RAY_MAX;

                return -b - sqrt(h);
            }

            void ray(out vec3 ray_org, out vec3 ray_dir, vec2 pos) {
                vec3 screen_d = u_screen_pos + pos.x * u_screen_right + pos.y * u_screen_up;
                ray_org = u_camera_pos;
                ray_dir = normalize(screen_d);
            }
            `;


        let full_screen_vert_src =
            `
            attribute vec2 v_position;
                        
            varying vec2 xy;
            
            void main(void) {
                xy = v_position;
                gl_Position = vec4(v_position, 0.0, 1.0);
            }
            `;


        let centered_vert_src =
            `
            attribute vec2 v_position;
    
            varying vec2 pos;
    
            void main(void) {
              pos = v_position * 2.0 - 1.0;
              gl_Position = vec4(pos, 0.0, 1.0);
            }
            `;

        let transformed_vert_src =
            `
            attribute vec2 v_position;
            
            uniform vec4 u_mat;

            varying vec2 pos;
            varying vec2 base_pos;
    
            void main(void) {
              base_pos = v_position;
              pos = v_position * u_mat.xy + u_mat.zw;
              gl_Position = vec4(pos, 0.0, 1.0);
            }
            `;


        let derivatives_preamble = `#extension GL_OES_standard_derivatives : enable`;

        // agx approximation from: https://iolite-engine.com/blog_posts/minimal_agx_implementation
        let complex_moon_frag_src =
            `

            precision highp float;

            uniform vec3 camera_pos;
            uniform vec3 screen_up;
            uniform vec3 screen_right;
            uniform vec4 light_dir;
            uniform vec3 screen_diff;
            uniform vec2 dxdy;
            uniform float earthlight;
            uniform vec3 sky_dir;
            uniform vec4 tint;

            uniform sampler2D tex_color;
            uniform sampler2D tex_height;
            uniform sampler2D tex_sky;


            varying vec2 pos;

            const float PI = 3.14159265359;
            const float RAY_MAX = 1.0e20;
            const float height_scale = 0.0113105153;


            float quick_sphere(vec3 ray_org, vec3 ray_dir) {

                       vec3 oc = ray_org;
                float b = dot(oc, ray_dir);
                float c = dot(oc, oc) - 1.0;
                float h = b*b - c;
                
                if (h<0.0) return RAY_MAX;

                return -b - sqrt(h);
            }

            float linear_to_srgb(float c) {
                return c < 0.0031308 ? 12.92 * c : 1.055 * pow(c, 1.0/2.4) - 0.055;
            }

            vec2 signNotZero(vec2 v) {
                return vec2((v.x >= 0.0) ? +1.0 : -1.0, (v.y >= 0.0) ? +1.0 : -1.0);
            }

            vec2 xyz_to_oct(vec3 v)
            {
                vec2 p = v.xy * (1.0 / (abs(v.x) + abs(v.y) + abs(v.z)));
                return (v.z <= 0.0) ? ((1.0 - abs(p.yx)) * signNotZero(p)) : p;
            }

            vec3 oct_to_xyz(vec2 e) {
                vec3 v = vec3(e.xy, 1.0 - abs(e.x) - abs(e.y));
                if (v.z < 0.0) v.xy = (1.0 - abs(v.yx)) * signNotZero(v.xy);
                    return normalize(v);
            }


            vec2 oct_to_coord(vec2 oct) {
                float pad = 2.0;
                float w = 1536.0;
                return  oct * (0.5 * (w - pad*2.0)/w) + (0.5 * (w - pad*2.0)/w + pad/w);
            }

            float height(vec2 oct) {
                vec2 coord = oct_to_coord(oct);
                float h = texture2D(tex_height, coord).r;
                return (1.0 - height_scale) + h * height_scale;
            }

            vec2 height_ratio(vec2 oct) {
                vec2 coord = oct_to_coord(oct);
                vec2 h = texture2D(tex_height, coord).ra;
                h.x = (1.0 - height_scale) + h.x * height_scale;
                return h;
            }

            vec3 normal_at_oct(vec2 oct)
            {
                float dlon = 1.0/1536.0 * 2.0;
                float dlat = 1.0/1536.0 * 2.0;

                float hx1 = height(oct + vec2(dlon, 0.0));
                float hx0 = height(oct - vec2(dlon, 0.0));

                float hy1 = height(oct + vec2(0.0, dlat));
                float hy0 = height(oct - vec2(0.0, dlat));

                vec3 x1 = oct_to_xyz(oct + vec2(dlon, 0.0));
                vec3 x0 = oct_to_xyz(oct - vec2(dlon, 0.0));

                vec3 y1 = oct_to_xyz(oct + vec2(0.0, dlat));
                vec3 y0 = oct_to_xyz(oct - vec2(0.0, dlat));


                float sdzdx = -(hx1 - hx0) * 0.5;
                float sdzdy = -(hy1 - hy0) * 0.5;


                vec3 norm_dir = oct_to_xyz(oct);
                vec3 stangent_dir = (x1 - x0);
                vec3 sbitangent_dir = (y1 - y0);

                vec3 tangent_dir = normalize(vec3(-norm_dir.y, norm_dir.x, 0.0));
                vec3 bitangent_dir = cross(norm_dir, tangent_dir);

                float m00 = dot(stangent_dir, tangent_dir);
                float m01 = dot(sbitangent_dir, tangent_dir);
                float m10 = dot(stangent_dir, bitangent_dir);
                float m11 = dot(sbitangent_dir, bitangent_dir);

                float sc = 1.0/(m00*m11 - m01*m10);

                float dzdx = (+sdzdx * m11 - sdzdy * m10) * sc;
                float dzdy = (-sdzdx * m01 + sdzdy * m00) * sc;

                vec3 norm = norm_dir;
                norm += dzdx * tangent_dir;
                norm += dzdy * bitangent_dir;
                norm = normalize(norm);

               return norm;
            }

            float radiance_factor(vec3 di, vec3 de, vec3 n, vec3 color) {

                float l = 0.21*color.g + 0.71*color.g + 0.08*color.b;
                
                l = sqrt(sqrt(l));
                l = 0.5;

                float b = mix(0.165, 0.270, 1.0 - l);
                float c = mix(0.0, 1.05, l);
                float hs = 0.06;
                float Bs0 = mix(1.52, 2.08, 1.0 - l);
                float w = mix(0.2, 0.52, l);

                float cosi = clamp(dot(di, n), 0.0, 1.0);
                float cose = clamp(dot(de, n), 0.0, 1.0);

                float cosg = clamp(dot(de, di), 0.0, 1.0);
                float sing = sqrt(1.0 - cosg*cosg);
                float tang2 = (1.0 - cosg) / (sing + 0.00001);


                float LS = cosi / (cosi + cose);

                float b2 = b * b;
                float pdenom0 = 1.0 - 2.0 * b * cosg + b2;
                float pdenom1 = 1.0 + 2.0 * b * cosg + b2;
                float p = (0.5 + 0.5 * c) * (1.0 - b2) / (pdenom0 * sqrt(pdenom0)) +
                          (0.5 - 0.5 * c) * (1.0 - b2) / (pdenom1 * sqrt(pdenom1));

                float Bs = 1.0 / (1.0 + tang2 / hs);

                float gamma = sqrt (1.0 - w);

                float Hi = (1.0 + 2.0*cosi) / (1.0 + 2.0*gamma*cosi);
                float He = (1.0 + 2.0*cose) / (1.0 + 2.0*gamma*cose);

                float M = Hi * He - 1.0;

                return LS * w * 0.25 * (p * (1.0 + Bs0*Bs) + M);
            }


            vec4 trace(vec3 ray_org, vec3 ray_dir) {
                float start_t = quick_sphere(ray_org, ray_dir);

                vec3 hit_start = ray_org + start_t * ray_dir;

                vec3 hit_pos = hit_start;
                float hit_h = length(hit_pos);

                const int cone_steps_limit = 10;
                const int shadow_cone_steps_limit = 12;
                const int bisect_limit = 4;
                    
                {
                    vec3 prev_pos = hit_pos;

                    for (int i = 0; i < cone_steps_limit; i++) {

                        float hit_pos_h = length(hit_pos);
                        
                        vec3 norm = hit_pos/hit_pos_h;
                        vec2 oct = xyz_to_oct(norm);
                        vec2 hr = height_ratio(oct);

                        float dh = -hr.r + hit_pos_h;

                        if (dh < 0.0) {
                            break;
                        }

                        float ratio_val = hr.g;

                        float ratio = 8.0 * ratio_val;
                        
                        float cosl = -dot(ray_dir, norm);
                        float sinl = sqrt(1.0 - clamp(cosl*cosl, 0.0, 1.0));

                        float d = (dh * ratio) / (sinl + cosl * ratio);

                        float l = max(d, 0.0015);
                                    
                        prev_pos = hit_pos;
                        hit_pos = hit_pos + ray_dir * l;
                    }                            

                     for (int i = 0; i < bisect_limit; i++) {

                        vec3 new_pos = mix(prev_pos, hit_pos, 0.5);
                        float new_pos_h = length(new_pos);
                        vec2 new_oct = xyz_to_oct(new_pos/new_pos_h);
                        float new_h = height(new_oct);

                        if (new_h > new_pos_h)
                            hit_pos = new_pos;
                        else
                            prev_pos = new_pos;
                    }
                }

                vec2 oct = xyz_to_oct(hit_pos);
                float h = height(oct);

                hit_pos = normalize(hit_pos) * h;

                float shadow = 1.0;

                {
                    float delta = 10000.0;

                    vec3 shadow_pos = hit_pos - light_dir.xyz * 0.0001;

                    for (int i = 0; i < shadow_cone_steps_limit; i++) {

                        float shadow_pos_h = length(shadow_pos);
                        
                        vec3 norm = shadow_pos/shadow_pos_h;
                        vec2 oct = xyz_to_oct(norm);
                        vec2 hr = height_ratio(oct);

                        float dh = -hr.r + shadow_pos_h;

                        delta = min(delta, dh);

                        float ratio = 4.0 * hr.g;
                        
                        float cosl = -dot(-light_dir.xyz, norm);
                        float sinl = sqrt(1.0 - clamp(cosl*cosl, 0.0, 1.0));

                        float d = (dh * ratio) / (sinl + cosl * ratio);
                                    
                        shadow_pos = shadow_pos - light_dir.xyz * max(d, 0.002);    
                    }

                    shadow = smoothstep(-0.0003, 0.0001, delta);
                }

                vec3 norm = normal_at_oct(oct);

                vec4 color = texture2D(tex_color, oct_to_coord(oct));
                color.rgb = convert_color(color.rgb);
                float hh = light_dir.w * radiance_factor(-light_dir.xyz, -ray_dir, norm, color.rgb);
                hh = clamp(hh, 0.0, 1.0);
                color.rgb *= (hh * shadow + vec3(earthlight));
            

                float a = 1.0;
            
                a *= smoothstep(-0.02, -0.025, dot(norm, ray_dir));

                return color * a;
            }

       
            vec3 agx(vec3 v) {

            const float min = -16.;
            const float max = 1.0;
            
            v = clamp(log2(v), min, max);
            v = (v - min) / (max - min);

            v  = (((((15.5 * v - 40.14) * v + 31.96) * v - 6.868) * v + 0.4298) * v + 0.1191) * v - 0.00232;
        
            return v;
            }

            void main(void) {

                vec4 color = vec4(0.0);

                color += trace(camera_pos, normalize((pos.x + dxdy.x) * screen_right + (pos.y + dxdy.y) * screen_up + screen_diff));
                
                color += trace(camera_pos, normalize((pos.x - dxdy.x) * screen_right + (pos.y - dxdy.y) * screen_up + screen_diff));

                color *= 0.5;

                color.rgb /= max(0.001, color.a);

                color.rgb = agx(color.rgb);


                if (sky_dir.z > 0.0)
                {
                   vec3 sky = texture2D(tex_sky, sky_dir.xy).rgb;

                    float sky_max = max(sky.r, max(sky.g, sky.b));
                
                    color.rgb *= 1.0 - sky_max * 0.9;
                }

                color.rgb *= tint.rgb;
                color.rgb *= color.a;


                gl_FragColor = color;
            }
          `;


        let elevation_moon_frag_src =
            `#extension GL_OES_standard_derivatives : enable

            precision highp float;

            uniform vec3 camera_pos;
            uniform vec3 screen_up;
            uniform vec3 screen_right;
            uniform vec3 light_dir;
            uniform vec3 screen_diff;
            uniform vec2 dxdy;
            uniform vec2 u_height_scale;

            uniform sampler2D tex_height;
            uniform sampler2D tex_color;

            varying vec2 pos;

            const float PI = 3.14159265359;
            const float RAY_MAX = 1.0e20;
            const float height_scale = 0.0113105153;


            float quick_sphere(vec3 ray_org, vec3 ray_dir) {

                vec3 oc = ray_org;
                float b = dot(oc, ray_dir);
                float c = dot(oc, oc) - 1.0;
                float h = b*b - c;
                
                if (h<0.0) return RAY_MAX;

                return -b - sqrt(h);
            }

            vec2 signNotZero(vec2 v) {
                return vec2((v.x >= 0.0) ? +1.0 : -1.0, (v.y >= 0.0) ? +1.0 : -1.0);
            }

            vec2 xyz_to_oct(vec3 v)
            {
                vec2 p = v.xy * (1.0 / (abs(v.x) + abs(v.y) + abs(v.z)));
                return (v.z <= 0.0) ? ((1.0 - abs(p.yx)) * signNotZero(p)) : p;
            }

            vec3 oct_to_xyz(vec2 e) {
                vec3 v = vec3(e.xy, 1.0 - abs(e.x) - abs(e.y));
                if (v.z < 0.0) v.xy = (1.0 - abs(v.yx)) * signNotZero(v.xy);
                    return normalize(v);
            }


            vec2 oct_to_coord(vec2 oct) {
                float pad = 2.0;
                float w = 1536.0;
                return  oct * (0.5 * (w - pad*2.0)/w) + (0.5 * (w - pad*2.0)/w + pad/w);
            }

            float height(vec2 oct) {
                vec2 coord = oct_to_coord(oct);
                float h = texture2D(tex_height, coord).r;
                return 1.0 + (h - 1.0) * height_scale * u_height_scale.x;
            }

            vec2 height_ratio(vec2 oct) {
                vec2 coord = oct_to_coord(oct);
                vec2 h = texture2D(tex_height, coord).ra;
                h.x = 1.0 + (h.x - 1.0) * height_scale * u_height_scale.x;
                return h;
            }


            vec4 trace(vec3 ray_org, vec3 ray_dir) {
                float start_t = quick_sphere(ray_org, ray_dir);

                vec3 hit_start = ray_org + start_t * ray_dir;

                vec3 hit_pos = hit_start;
                float hit_h = length(hit_pos);

                const int cone_steps_limit = 23;
                const int bisect_limit = 4;
                    
                {
                    vec3 prev_pos = hit_pos;

                    for (int i = 0; i < cone_steps_limit; i++) {

                        float hit_pos_h = length(hit_pos);
                        
                        vec3 norm = hit_pos/hit_pos_h;
                        vec2 oct = xyz_to_oct(norm);
                        vec2 hr = height_ratio(oct);

                        float dh = -hr.r + hit_pos_h;

                        if (dh < 0.0) {
                            break;
                        }

                        float ratio_val = hr.g;

                        float ratio = (8.0 * u_height_scale.y) * ratio_val;
                        
                        float cosl = -dot(ray_dir, norm);
                        float sinl = sqrt(1.0 - clamp(cosl*cosl, 0.0, 1.0));

                        float d = (dh * ratio) / (sinl + cosl * ratio);

                        float l = max(d, 0.0015);
                                    
                        prev_pos = hit_pos;
                        hit_pos = hit_pos + ray_dir * l;
                    }                            

                     for (int i = 0; i < bisect_limit; i++) {

                        vec3 new_pos = mix(prev_pos, hit_pos, 0.5);
                        float new_pos_h = length(new_pos);
                        vec2 new_oct = xyz_to_oct(new_pos/new_pos_h);
                        float new_h = height(new_oct);

                        if (new_h > new_pos_h)
                            hit_pos = new_pos;
                        else
                            prev_pos = new_pos;
                    }
                }

                vec2 oct = xyz_to_oct(hit_pos);
                float h = height(oct);

                float hit_pos_h = length(hit_pos);
                hit_pos = normalize(hit_pos) * h;
   
                float hh = (h - (1.0 - height_scale * u_height_scale.x)) * u_height_scale.y / height_scale;
                
                vec4 color = texture2D(tex_color, vec2(hh, 0));
                                     
                float a = 1.0;

                if (hit_pos_h >= 1.0)
                    a = 0.0;

                return color * a;
            }

            void main(void) {

                vec4 color = vec4(0.0);

                color += trace(camera_pos, normalize((pos.x + dxdy.x) * screen_right + (pos.y + dxdy.y) * screen_up + screen_diff));

                color += trace(camera_pos, normalize((pos.x - dxdy.x) * screen_right + (pos.y - dxdy.y) * screen_up + screen_diff));

                color *= 0.5;


                gl_FragColor = color;
            }
          `;



        let color_fill_frag_src =
            `
                precision mediump float;
                
                varying vec2 xy;

                uniform vec4 u_color;
                            
                void main(void) {
                    gl_FragColor = u_color;
                }
            `;


        let eclipse_frag_src =
            `
                precision mediump float;
                
                varying vec2 pos;

            #define pi 3.141592653589793


            float hash(float p, float t)
            {
                vec2 p3 = vec2(p, t);
                p3  = fract(p3*0.1031);
                p3 += dot(p3, p3.yx+31.32);
                return fract((p3.x)*p3.y);
            }

            float noise(float p, float t)
            {
                vec2 b = vec2(floor(p), ceil(p));
                float f = smoothstep(0.0, 1.0, fract(p));
                return mix(hash(b.x, t), hash(b.y, t), f);
            }

            float fbm(float pos)
            {
                float value = 0.0;
                float scale = 1.0;
                float atten = 0.5;
                float t = 0.0;
                for(int i = 0; i < 4; i++)
                {
                    t += atten;
                    value += noise(pos*scale, float(i))*atten;
                    scale *= 2.0;
                    atten *= 0.5;
                }
                return value/t;
            }


            float t(vec2 uv, float g)
            {

                float a0 = atan(uv.y, uv.x);
                float a1 = atan(uv.y, -uv.x);
                
                float l = length(uv);
                float c = 0.0;

                float c0 = smoothstep(-pi, 0.0, a0) - smoothstep(0.0, pi, a0);
                float c1 = smoothstep(-pi, 0.0, a1) - smoothstep(0.0, pi, a1);

                float r0 = 0.0;
                r0 += fbm(a0*2. + g) * c0;
                r0 += fbm(a1*2. + 3.0 + g) * c1;
                
                float r1  = 0.0;
                r1 += fbm(a0*0.5 + 1.0 + g) * c0;
                r1 += fbm(a1*0.5 + 20.0 + g) * c1;
                
                float m0 = (l - 0.4) / (r1 * 5.0);
                m0 = clamp(m0, 0.0, 1.0);
                
                m0 = 1.0 - m0;
                m0 = (m0*m0);

                float d0 = (l - 0.9) / (1.0 + r1*3.0);
                d0 = clamp(d0, 0.0, 1.0);

                d0 = 1.0 - d0;
                d0 = (d0*d0);
                d0 = (d0*d0);
                
                c += 0.06*d0;
                c += r0 * m0;
            
            return c;
            }
         
                void main(void) {
                    vec2 uv = vec2(-pos.y, pos.x) * 3.0;
                    
                    float l = length(uv);

                    
                    float c = 0.0;
                    c += t(uv,0.0);
                    c += t(uv + vec2(0.1,-0.3), 3.0);
                    c += t(uv + vec2(-0.4,0.2), 6.0);
                    c += t(uv + vec2(-0.1,-0.2), 11.0);
                    c += t(uv + vec2(0.4,0.4), 163.0);
                    c += t(uv + vec2(-0.4,-0.2), 32.4);
                    c += t(uv + vec2(0.3,0.2), 94.0);
                    c += t(uv + vec2(-0.3,-0.2), 14.0);
                    c -= 1.5*t(uv + vec2(-0.1,0.15), 152.4);
                    c *= 0.6;
                    c = 0.5 * c*c + c;
                    c *= 0.24;
                    
                    float h = 1.0 - clamp((l - 1.1)/(2.0-0.9), 0.0, 1.0);
                    
                    c += 0.2 * h * h;
                                        
                    float a = atan(uv.y, uv.x);
                        float g = fbm(a*3.0 + 28.9);

                    float p = 0.0;
                    {
                    float t0 = clamp((a - 0.1)/0.1, 0.0, 1.0);
                    float r1 = 1.0+ (0.8) * t0*(1.0-t0)* t0*(1.0-t0);
                    float r0 = 1.0+ (0.2) * t0*(1.0-t0)* t0*(1.0-t0);
                    p += (step(r0, l) - step(r1, l));
                    }   

                    {
                    float t0 = 1.0 - clamp((a - 1.4)/0.2, 0.0, 1.0);
                    float r1 = -0.02+ 1.0+ 0.16*(0.13 + 0.3*g) * (sqrt(sqrt(t0))+ 1.6*t0*t0*t0) * (1.0 - t0*t0*t0*t0*t0);
                    float r0 = -0.02+ 0.96+  0.19*(0.4) * (sqrt(sqrt(t0)));

                    p += clamp(step(r0, l) - step(r1, l), 0.0, 1.0) * g;
                }
                    
                    c = min(1.0, c);
                    
                    vec3 col = vec3(c);

                        col += p * vec3(1.0, 0.1, 0.1);


                    col *= smoothstep(0.99, 1.0, l);
                    

                    gl_FragColor = vec4(col,1.0);
                }
            `;


        let sun_rays_frag_src =
            `
                precision mediump float;
                
            varying vec2 base_pos;

            uniform vec4 u_color;
            uniform float u_seed;

            #define pi 3.141592653589793


            float hash(float p, float t)
            {
                vec2 p3 = vec2(p, t);
                p3  = fract(p3*0.1031);
                p3 += dot(p3, p3.yx+31.32);
                return fract((p3.x)*p3.y);
            }

            float noise(float p, float t)
            {
                vec2 b = vec2(floor(p), ceil(p));
                float f = smoothstep(0.0, 1.0, fract(p));
                return mix(hash(b.x, t), hash(b.y, t), f);
            }

            float fbm(float pos)
            {
                float value = 0.0;
                float scale = 1.0;
                float atten = 0.5;
                float t = 0.0;
                for(int i = 0; i < 4; i++)
                {
                    t += atten;
                    value += noise(pos*scale, float(i))*atten;
                    scale *= 2.0;
                    atten *= 0.5;
                }
                return value/t;
            }


                void main(void) {

                    float r = length(base_pos.xy);

                    float angle = atan(base_pos.x, base_pos.y);
                    
                    float dr = fbm(10.0 * angle + u_seed);

                    float a = 0.0;
                    a += 1.0 * smoothstep(0.3, 1.0 - dr * 0.5, r);
                    a += 1.0 * smoothstep(0.1, 0.9, r);
                    a = 1.0 - a/2.0;
                    a = a * a * a;
                    
                    a *= 0.8;
                    
                    gl_FragColor = u_color * a;
                }
            `;


        let blob_vert_src =
            `
            attribute vec2 v_pos;
            attribute float v_id;

            uniform mat4 u_mvp;
            uniform float u_size;

            varying float id;

            void main(void) {
                    
                id = v_id;

                gl_Position = u_mvp * vec4(v_pos, 0.0, 1.0);
                gl_PointSize = u_size;
            }
            `;

        let blob_frag_src =
            `
                precision mediump float;
                
                varying float id;

                uniform float u_n_threshold;
                uniform vec4 u_color0;
                uniform vec4 u_color1;
                            

                float hash(float p) { p = fract(p * 0.0112); p *= p + 4.123; p *= p + p; return fract(p); }

                void main(void) {

                    vec2 xy = gl_PointCoord - 0.5;
                    vec2 axy = abs(xy);
                    float a = min(axy.x, axy.y) / max(0.01, max(axy.x, axy.y));

                    a += xy.x < 0.0 ? 1.0 : 0.0;
                    a += xy.y < 0.0 ? 2.0 : 0.0;

                    float r2 = dot (xy, xy);
                    float r = 2.0 * sqrt(r2);

                    r = r * 1.3 + 0.1 * sin(a * 5.0 + id) + 0.2 * sin(a * 0.5 + id);

                    vec4 color = id < u_n_threshold ? u_color0 : u_color1;
 
                    color.rgb *= 0.95 + 0.05 * hash(id);
                    color.rgb *= 1.0 - 0.1 * smoothstep(0.3, 1.0, r);
                    color *= 1.0 - smoothstep(0.8, 1.0, r);

                    gl_FragColor = color;
                }
            `;


        let mesh_vert_src =
            `
            attribute vec2 v_pos;

            uniform mat4 u_mvp;
            uniform vec4 u_params;

            varying float z;
            varying float r;

            void main(void) {
            
                r = length(v_pos);
                float arg = r * u_params.x - u_params.y;
                float a0 = clamp(3.0 * sin(arg * 0.25), 0.0, 1.0);
                z = a0 * 0.04 * sin(arg) / (r + 0.14);
                gl_Position = u_mvp * vec4(v_pos, z, 1.0);
            }
            `;

        let mesh_frag_src =
            `
                precision mediump float;
                
                varying float z;
                varying float r;
       
                void main(void) {
 
                 vec4 c = z > 0.0 ? vec4(0.89,0.21,0.14,1) : vec4(0.0,0.56,1.0,1);
           
                 c *= abs(z * 8.0) * (1.0 - smoothstep(0.9, 1.0, r));

                 gl_FragColor = c;
                }
            `;


        let land_vert_src =
            `
            attribute vec2 v_pos;

            uniform mat4 u_mvp;
            uniform vec2 u_seed;

            varying vec2 uv;
            varying float z;

            void main(void) {

                uv = v_pos;

                float a = v_pos.x * 2.0 * 3.1415926535;
                float r = 0.75 + 0.25 * (1.0 - v_pos.y);
 
                vec3 pos = vec3(r * cos(a), r * sin(a), 0.0);
                z = cos(a * 39.0 + u_seed.x) * sin(50.0 + a* 30.0 + r * 20.0 + u_seed.y);

                z = mix(z, -1.7, smoothstep(0.7, 0.9, v_pos.y));

                pos.xy *= 1e6;
                pos.z = 9000.0 * z;
                gl_Position = u_mvp * vec4(pos, 1.0);
            }
            `;

        let land_frag_src =
            `
                precision mediump float;
                
                uniform vec4 u_color;
                uniform sampler2D u_tex_noise;

                varying vec2 uv;
                varying float z;

                float noise() {
                    float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                    return n * (1.5/255.0) - 0.75/255.0;
                }

                void main(void) {
 
                vec4 c = u_color;
                c.rgb *= 0.3 + 0.7 * (z * 0.5 + 0.5);

                c.rgb += noise();
                c *= 1.0 - smoothstep(0.8, 0.9, uv.y);
                

                 gl_FragColor = c;
                }
            `;



        let trail_vert_src =
            `
            attribute vec2 v_pos;
            attribute vec3 v_p0;
            attribute vec3 v_p1;
            attribute float v_id;

            varying float color_a;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;
            uniform vec2 u_params;
            uniform vec3 u_offset;
            uniform vec4 u_alpha_range;

            void main(void) {
                    
                float t = v_pos.y * 0.5 + 0.5;
                vec3 pos = mix(v_p0, v_p1, t);

                pos += u_offset;

                float ta = v_id + t;
                color_a = smoothstep(u_alpha_range.x, u_alpha_range.y, ta) - 
                          smoothstep(u_alpha_range.z, u_alpha_range.w, ta);
         
                vec4 position = u_mvp * vec4(pos, 1.0);
                position *= (1.0 / max(0.00001, position.w));
                
                vec3 dir = v_p1 - v_p0;
                vec3 normal = (u_mvp * vec4(dir, 0.0)).xyz;
        
                vec2 ss_normal = normalize(normal.xy);

                float perp_sign = v_pos.x;
                float width = u_params.x;
                position.x += width * ss_normal.y * -perp_sign;
                position.y += width * ss_normal.x * perp_sign * u_params.y;

                gl_Position = position;
            }
            `;

        let trail_frag_src =
            `
                precision mediump float;
                
                varying vec2 xy;
                varying float color_a;

                uniform vec4 u_color;
                            
                void main(void) {
                    gl_FragColor = u_color * color_a;
                }
            `;

        let quad_vert_src =
            `
            attribute vec2 v_pos;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;

            varying vec2 uv;

            void main(void) {

                uv = v_pos;

                gl_Position = u_mvp * vec4(v_pos, 0.0, 1.0);
            }
            `;

        let disc_frag_src =
            `
            precision mediump float;
            
            varying vec2 uv;

            uniform vec4 u_color;
            uniform vec4 u_coords;
            uniform float u_feather;
                        
            void main(void) {
                vec2 xy = uv * u_coords.xy + u_coords.zw;
                float r = length(xy);
                gl_FragColor = u_color * (1.0 - smoothstep(u_feather, 1.0, r));
            }
        `;


        let shaded_mesh_vert_src =
            `
        attribute vec3 v_pos;
        attribute vec3 v_norm;
        attribute float v_shade;
            
        uniform mat4 u_mvp;
        uniform mat3 u_rot;

        varying float shade;

        void main(void) {

            shade = 0.1 + 0.9 * max(0.0, (u_rot * v_norm).z);

            shade *= v_shade;

            gl_Position = u_mvp * vec4(v_pos, 1.0);
        }
        `;

        let shaded_mesh_frag_src =
            `
        precision mediump float;

        varying float shade;

        uniform vec4 u_color;

        void main(void) {

            vec4 c = u_color;
            c.rgb *= sqrt(shade);
        
            gl_FragColor = c;
        }
    `;


        let dummy_frag_src =
            `
            precision mediump float;
                                    
            void main(void) {
                gl_FragColor = vec4(1.0, 0.0, 1.0, 1.0);
            }
        `;

        let hapke_cosine_brdf =
            `
            float radiance(vec3 di, vec3 de, vec3 n) {

                float b = 0.23;
                float c = 0.6;
                float hs = 0.06;
                float Bs0 = 1.8;
                float w = 0.4;
                float K = 1.0;
                float gamma = sqrt (1.0 - w);

                float cosi = clamp(dot(di, n), 0.0, 1.0);
                float cose = clamp(-dot(de, n), 0.0, 1.0);

      
                float cosg = clamp(-dot(de, di), 0.0, 1.0);
                float sing = sqrt(1.0 - cosg*cosg);
                float tang2 = (1.0 - cosg) / (sing + 0.00001);
                
                float LS = cosi / (cosi + cose);

                float b2 = b * b;
                float pdenom0 = 1.0 - 2.0 * b * cosg + b2;
                float pdenom1 = 1.0 + 2.0 * b * cosg + b2;
                float p = (0.5 + 0.5 * c) * (1.0 - b2) / (pdenom0 * sqrt(pdenom0)) +
                          (0.5 - 0.5 * c) * (1.0 - b2) / (pdenom1 * sqrt(pdenom1));
      
                float Bs = 1.0 / (1.0 + tang2 / hs);
      
      
                float Hi = (1.0 + 2.0*cosi/K) / (1.0 + 2.0*gamma*cosi/K);
                float He = (1.0 + 2.0*cose/K) / (1.0 + 2.0*gamma*cose/K);
      
                float M = Hi * He - 1.0;
      
                return LS * K * w * 0.25 * (p * (1.0 + Bs0*Bs) + M) * 0.4 / 0.629197;
              }
            `

        let lambert_cosine_brdf =
            `
            float radiance(vec3 di, vec3 de, vec3 n) {
                float w = 0.4;
                return w * dot(di, n) * (1.0 / PI);
              }
            `

        let brdf_sphere_frag_src =
            `
            varying vec2 xy;

            uniform float u_marker;
                        
            void main(void) {

                vec3 ray_org, ray_dir;
                ray(ray_org, ray_dir, xy);
                
                float start_t = quick_sphere(ray_org, ray_dir, vec3(0.0), 1.0);
      
                vec3 hit = normalize(ray_org + start_t * ray_dir);

                float intensity = 2.6;
                float cosine = dot(hit, u_light_dir);

                float shade = intensity * radiance(u_light_dir, ray_dir, hit);

                shade = linear_to_srgb(shade);
                shade = noise(shade);

                float alpha = start_t == RAY_MAX ? 0.0 : 1.0;
                alpha *= smoothstep(0.0, 0.1, dot(hit, -ray_dir));

                vec3 color = vec3(shade);

                vec3 circ_loc = vec3(1.0, 0.0, 0.0);

                float d = length(cross(circ_loc, hit));
                float dd = min(0.03, fwidth(d)*1.5);
                float rim = smoothstep(0.035 - dd, 0.035, d) -
                            smoothstep(0.04, 0.04 + dd, d);

                rim *= u_marker * (dot(circ_loc, hit) > 0.0 ? 1.0 : 0.0);

                color = mix(color, vec3(0.15, 0.42, 0.73), rim);

                gl_FragColor = vec4(color * alpha, alpha);
            }
            `;

        let tetra_vert_src =
            `
            attribute vec3 v_pos0;
            attribute vec3 v_pos1;
            attribute vec3 v_pos2;
            attribute vec3 v_pos3;

            attribute vec4 v_weight;
            attribute vec4 v_n_weight;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;
            uniform vec3 u_light_dir;

            varying mediump float shade;

            void main(void) {

                vec3 pos = v_pos0 * v_weight.x +
                           v_pos1 * v_weight.y +
                           v_pos2 * v_weight.z +
                           v_pos3 * v_weight.w;

                vec3 n = cross(v_pos1 - v_pos0, v_pos3 - v_pos0) * v_n_weight.x +
                         cross(v_pos2 - v_pos0, v_pos1 - v_pos0) * v_n_weight.y +
                         cross(v_pos3 - v_pos0, v_pos2 - v_pos0) * v_n_weight.z +
                         cross(v_pos2 - v_pos1, v_pos3 - v_pos1) * v_n_weight.w;

                float d = dot(normalize(n), u_light_dir);
                shade = 0.0049 + 0.9951 * max(0.0, d);
                shade = sqrt(shade);

                gl_Position = u_mvp * vec4(pos, 1.0);
            }
            `;

        let tetra_frag_src =
            `        
            precision mediump float;

            varying mediump float shade;

            void main(void) {
                vec4 c = vec4(1.0);
                c.rgb *= shade;
                gl_FragColor = c;
            }
            `;

        let star_vert_src =
            `
            attribute vec4 v_xyzm;
           
            uniform mat4 u_mvp;

            varying mediump float mag;

            void main(void) {

                mag = v_xyzm.w;
                gl_Position = u_mvp * vec4(v_xyzm.xyz * 1000000.0, 1.0);
                gl_PointSize = max(3.0, min(5.0, mag * 40.0));
            }
            `;

        let star_frag_src =
            `        
            precision mediump float;

            varying mediump float mag;

            void main(void) {

            
                vec2 xy = gl_PointCoord * 2.0 - 1.0;
                float r = sqrt(dot(xy, xy));

                float a = 1.0 - smoothstep(0.5, 1.0, r);

                a *= min(1.0, mag * 30.0);
                a = sqrt(a);

                gl_FragColor = vec4(a);
            }
            `;


        // ugly
        let tetra_prism_vert_src =
            `
            attribute vec3 v_pos0;
            attribute vec3 v_pos1;
            attribute vec3 v_pos2;
            attribute vec3 v_pos3;

            attribute vec4 v_weight;
            attribute vec4 v_n_weight;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;
            uniform vec3 u_light_dir;

            varying mediump float shade;

            void main(void) {

                vec3 n0 = cross(v_pos1 - v_pos0, v_pos3 - v_pos0);
                vec3 n1 = cross(v_pos2 - v_pos0, v_pos1 - v_pos0);
                vec3 n2 = cross(v_pos3 - v_pos0, v_pos2 - v_pos0);
                vec3 n3 = cross(v_pos2 - v_pos1, v_pos3 - v_pos1);

                float c0 = dot(n0, u_light_dir);
                float c1 = dot(n1, u_light_dir);
                float c2 = dot(n2, u_light_dir);
                float c3 = dot(n3, u_light_dir);

                float count = ((c0 > 0.0) ? 1.0 : 0.0) + 
                              ((c1 > 0.0) ? 1.0 : 0.0) + 
                              ((c2 > 0.0) ? 1.0 : 0.0) + 
                              ((c3 > 0.0) ? 1.0 : 0.0);

                if (count == 3.0) {
                    c0 = -c0;
                    c1 = -c1;
                    c2 = -c2;
                    c3 = -c3;
                }

                vec3 p0, p1, p2, p3;

                p0 = v_pos0;

                if (c0 > 0.0) {
                    if (c1 > 0.0) {
                        p1 = v_pos3;
                        p2 = v_pos1;
                        p3 = v_pos2;
                    } else if (c2 > 0.0) {
                        p1 = v_pos2;
                        p2 = v_pos3;
                        p3 = v_pos1;
                    } else if (c3 > 0.0) {
                        p1 = v_pos3;
                        p2 = v_pos2;
                        p3 = v_pos1;
                    } else {
                        p1 = v_pos3;
                        p2 = v_pos1;
                        p3 = v_pos1;
                    }
                } else if (c1 > 0.0) {
                    if (c2 > 0.0) {
                        p1 = v_pos1;
                        p2 = v_pos2;
                        p3 = v_pos3;
                    } else if (c3 > 0.0) {
                        p1 = v_pos1;
                        p2 = v_pos3;
                        p3 = v_pos2;
                    } else {
                        p1 = v_pos1;
                        p2 = v_pos2;
                        p3 = v_pos2;
                    }
                } else if (c2 > 0.0) {          
                    if (c3 > 0.0) {
                        p1 = v_pos2;
                        p2 = v_pos1;
                        p3 = v_pos3;
                    } else {
                        p1 = v_pos2;
                        p2 = v_pos3;
                        p3 = v_pos3;
                    }
                } else {
                    p0 = v_pos2;
                    p1 = v_pos1;
                    p2 = v_pos3;
                    p3 = v_pos3;
                }

                if (count == 3.0) {
                    p3 = p1;
                    p1 = p0;
                    p0 = p3; 
                }

                vec3 pos = p0 * abs(v_weight.x) +
                           p1 * abs(v_weight.y) +
                           p2 * abs(v_weight.z) +
                           p3 * abs(v_weight.w);

                float sum = v_weight.x + v_weight.y + v_weight.z + v_weight.w;

                pos -= u_light_dir * 2.5 * (sum > 0.0 ? 1.0 : 0.0);

                gl_Position = u_mvp * vec4(pos, 1.0);
            }
            `;

        let tetra_prism_frag_src =
            `        
            precision mediump float;

            varying mediump float shade;

            void main(void) {
                vec4 c = vec4(0.0, 1.0, 0.0, 1.0);
                gl_FragColor = c;
            }
            `;





        let texture_dump_frag_src =
            `
            precision mediump float;

            varying vec2 xy;

            uniform sampler2D u_tex;
            uniform vec3 u_scale;


            void main(void) {

                vec2 uv = xy * 0.5 + 0.5;
                uv *= u_scale.xy;

                vec4 c = texture2D(u_tex, uv) * u_scale.z;

                gl_FragColor = vec4(c);
            }
            `;



        let plain_sphere_vert_src =
            `
            attribute vec3 v_pos;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;

            varying highp float shade;


            void main(void) {

                shade = 1.0;

                gl_Position = u_mvp * vec4(v_pos, 1.0);
            }
            `;

        let plain_sphere_frag_src =
            `        
            precision mediump float;

            uniform vec4 u_color;

            varying highp float shade;


            void main(void) {
                vec4 c = u_color;
                c.rgb *= shade;
                gl_FragColor = c;
            }
            `;


        let hemi_sphere_vert_src =
            `
            attribute vec3 v_pos;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;

            varying highp float z;


            void main(void) {

                z = v_pos.z;

                gl_Position = u_mvp * vec4(v_pos, 1.0);
            }
            `;

        let hemi_sphere_frag_src =
            `        
            precision mediump float;

            uniform vec4 u_color;

            varying highp float z;

            void main(void) {
                vec4 c = u_color;
                c *= smoothstep(-0.1, 0.1, z);
                gl_FragColor = c;
            }
            `;


        let sphere_vert_src =
            `
            attribute vec3 v_pos;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;

            varying highp vec3 pos;
            varying highp vec3 norm;

            void main(void) {

                pos = v_pos;
                norm = u_rot * v_pos;
                gl_Position = u_mvp * vec4(v_pos, 1.0);
            }
            `;

        let shaded_sphere_frag_src =
            `        
            precision mediump float;

            uniform vec4 u_color;

            varying highp vec3 pos;
            varying highp vec3 norm;


            void main(void) {
                vec4 c = u_color;
         
                c.rgb *= sqrt(norm.z);
                gl_FragColor = c;
            }
            `;

        let sun_eclipse_frag_src =
            `#extension GL_OES_standard_derivatives : enable        
            precision mediump float;


            varying highp vec3 pos;
            varying highp vec3 norm;

            uniform vec4 u_dir0;
            uniform vec4 u_dir1;
            uniform vec4 u_dir2;
            uniform float u_dim;

            uniform sampler2D u_tex_noise;


            float noise() {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return n * (1.5/255.0) - 0.75/255.0;
            }


            float spot(vec3 p, vec3 dir, float h) {

                float f = dot(dir, p);
  
                float w = fwidth(f);
                float r0 = 0.9999;
                float r1 = 0.99999;
                return 1.0 - h * (0.2 * smoothstep(r0 - w, r0, f) + 0.8 * smoothstep(r1 - w, r1, f));
            }

            void main(void) {
   
                vec3 p = normalize(pos);

                vec3 c0 = vec3(0.99, 0.71, 0.2);
                vec3 c1 = vec3(0.74, 0.25, 0.0);

                float t = 1.0 - norm.z;
                vec3 c = mix(c0, c1, 0.5*(t*t + t));


                c *= spot(p, u_dir0.xyz, u_dir0.w);
                c *= spot(p, u_dir1.xyz, u_dir1.w);
                c *= spot(p, u_dir2.xyz, u_dir2.w);

                c *= u_dim;

                c += noise();

                gl_FragColor = vec4(c, 1.0);
            }
            `;

        let tidal_water_vert_src =
            `
            attribute vec3 v_pos;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;

            uniform vec4 u_p0;
            uniform vec4 u_p1;
            uniform vec4 u_params;

            varying highp vec3 pos;
            varying highp vec3 norm;

            void main(void) {

                pos = v_pos + u_p0.xyz * ((dot(v_pos, u_p0.xyz)) * u_p0.w);

                norm = u_rot * v_pos;
                gl_Position = u_mvp * vec4(pos, 1.0);
            }
            `;

        let tidal_water_frag_src =
            `        
            precision mediump float;

            uniform vec4 u_color;

            varying highp vec3 pos;
            varying highp vec3 norm;


            void main(void) {

                vec4 c = u_color;

                c *= 0.5 + 0.5 * smoothstep(0.2, 0.8, norm.z);

                gl_FragColor = c;
            }
            `;


        let parted_sphere_vert_src =
            `
            attribute vec3 v_pos;
                
            uniform mat4 u_mvp;
            uniform mat3 u_rot;
            uniform vec3 u_spread;

            varying highp vec3 pos;
            varying float shade;

            void main(void) {

                vec3 p = v_pos;



                vec3 signs = vec3(p.x > 0.0 ? 1.0 : p.x < 0.0 ? -1.0 : 0.0,
                                  p.y > 0.0 ? 1.0 : p.y < 0.0 ? -1.0 : 0.0,
                                  p.z > 0.0 ? 1.0 : p.z < 0.0 ? -1.0 : 0.0);

                p = abs(p);
                p -= 1.0;
                vec3 norm = p * signs;

                p += u_spread;
                p *= signs;

                shade = 0.2 + 0.8 * max(0.0, (u_rot * norm).z);

                gl_Position = u_mvp * vec4(p, 1.0);
            }
            `;


        let parted_sphere_frag_src =
            `        
            precision mediump float;

            uniform vec4 u_color;

            varying float shade;


            void main(void) {
                vec4 c = u_color;

                c.a = 1.0;
                c.rgb *= sqrt(shade);
                
                c.rgb = mix(vec3(0.4, 0.2, 0.2), c.rgb, u_color.a);

                gl_FragColor = c;
            }
            `;


        let oct_frag_src =
            `
            vec2 sign_not_zero(vec2 v) {
                return vec2((v.x >= 0.0) ? +1.0 : -1.0, (v.y >= 0.0) ? +1.0 : -1.0);
            }

            vec2 xyz_to_oct(vec3 v) {
                vec2 p = v.xy * (1.0 / (abs(v.x) + abs(v.y) + abs(v.z)));
                return (v.z <= 0.0) ? ((1.0 - abs(p.yx)) * sign_not_zero(p)) : p;
            }

            vec2 oct_to_coord(vec2 oct, float w, float pad) {
                return (oct * 0.5 + 0.5) * ((w - pad*2.0)/w) + (pad/w);
            }
        `

        let earth_sdf_frag_src =
            `#extension GL_OES_standard_derivatives : enable

            precision mediump float;

            uniform sampler2D u_tex_base;
            uniform float u_clear;

            varying highp vec3 pos;

            `
            + oct_frag_src + ``
            + srgb_frag_src +

            `
            void main(void) {
                vec4 c = vec4(0.0, 0.0, 0.0, 1.0);

                float d = texture2D(u_tex_base, oct_to_coord(xyz_to_oct(pos), 256.0, 1.0)).r;
                float dw = fwidth(d) * 0.5;
                d = smoothstep(0.5 - dw, 0.5 + dw, d);
                d = 0.05 * d + 0.01;
                
                d = linear_to_srgb(d);

                d *= (1.0 - u_clear * 0.7);
                c.rgba = vec4(d, d, d, mix(1.0, d, u_clear));

                gl_FragColor = c;
            }
            `;


        let earth_sdf_eclipse_light_frag_src =
            `#extension GL_OES_standard_derivatives : enable

            uniform sampler2D u_tex_base;

            precision highp float;

            uniform vec3 u_sun;
            uniform vec3 u_moon;

            varying highp vec3 pos;

            `
            + oct_frag_src + ``
            + srgb_frag_src +

            `
            void main(void) {
                vec4 c = vec4(0.25, 0.2, 0.1, 0.3);


                float ER = 6371.0;
                float SR = 695700.0;
                float MR = 1737.4;

                vec3 p = normalize(pos) * ER;

                vec3 to_sun = -p + u_sun;
                vec3 to_moon = -p + u_moon;

                float s_sin = SR/length(to_sun);
                float s_cos = sqrt(1.0 - s_sin*s_sin);
                float sr = s_sin / s_cos;

                float m_sin = MR/length(to_moon);
                float m_cos = sqrt(1.0 - m_sin*m_sin);
                float mr = m_sin / m_cos;

                float m_s_sin = clamp(length(cross(normalize(to_sun), normalize(to_moon))), 0.0, 1.0);
                float m_s_cos = sqrt(1.0 - m_s_sin * m_s_sin);
                float d = m_s_sin / m_s_cos;

                float delta = 0.25 * sqrt((-d + sr + mr) * (d - sr + mr) * (d + sr - mr) * (d + sr + mr));

                float A = sr * sr * acos((d*d + sr*sr - mr*mr) / (2.0 * d * sr)) +
                          mr * mr * acos((d*d + mr*mr - sr*sr) / (2.0 * d * mr)) -
                          2.0 * delta;

                float f = 1.0 - clamp(A / (3.1415926535 * sr * sr), 0.0, 1.0);
                if (d < mr - sr)
                    f = 0.0;
                if (sr > mr && d < sr - mr) 
                    f = 1.0 - mr * mr / (sr * sr);

                c *= f;

                float a = clamp(dot(normalize(to_sun), pos), 0.0, 1.0);
                c *= a;

                {
                float d = texture2D(u_tex_base, oct_to_coord(xyz_to_oct(pos), 256.0, 1.0)).r;
                float dw = fwidth(d) * 0.5;
                d = smoothstep(0.5 - dw, 0.5 + dw, d);
                d = 0.05 * d + 0.01;
                                
                c = vec4(d, d, d, 1.0) * (1.0 - c.a) + c;

                c.r = linear_to_srgb(c.r);
                c.g = linear_to_srgb(c.g);
                c.b = linear_to_srgb(c.b);
                }

                 vec4 ring = vec4(0.0);

                float d0 = d - mr - sr;
                float dd0 = fwidth(d0);

                ring += (smoothstep(-dd0*2.0 , -dd0 * 0.5, d0) - smoothstep(dd0 * 0.5, dd0*2.0, d0)) 
                        * vec4(0.93, 0.50, 0.22, 1.0);
 
                float d1 = d - mr + sr;
                float dd1 = fwidth(d1);

                ring += (smoothstep(-dd1*2.0 , -dd1 * 0.5, d1) - smoothstep(dd1 * 0.5, dd1*2.0, d1)) 
                        * vec4(0.145, 0.419, 0.725, 1.0);

                ring *= a;
                c = c * (1.0 - ring.a) + ring;


                gl_FragColor = c;
            }
            `;


        let sample_tex_preamble =
            lod_ext ?
                `#extension GL_EXT_shader_texture_lod : enable
        #extension GL_OES_standard_derivatives : enable

        #define LEVELS 1
        
        lowp vec4 sample_texture(sampler2D tex, highp vec2 uv, highp float level) {
            return texture2DLodEXT(tex, uv, level);
        }
        `
                :
                `
        lowp vec4 sample_texture(sampler2D tex, highp vec2 uv, highp float level) {
            return texture2D(tex, uv);
        }
        `

        let earth_simple_frag_src =
            `        
            precision mediump float;

            uniform vec2 u_blur;
            uniform sampler2D u_tex_base;
            uniform sampler2D u_tex_clouds;
            uniform sampler2D u_tex_noise;

            varying highp vec3 pos;
            varying highp vec3 norm;

            float noise() {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return n * (1.5/255.0) - 0.75/255.0;
            }`
            + oct_frag_src +
            `
            vec3 rot(vec3 pos){

                vec3 p = pos;
                p.x = pos.x * u_blur.x - pos.y * u_blur.y;
                p.y = pos.x * u_blur.y + pos.y * u_blur.x;
                return p;
            }

            void main(void) {
                vec4 c = vec4(0.0, 0.0, 0.0, 1.0);

                vec3 rot_p = pos;

            #if LEVELS
                float z = norm.z;
                float level = dFdx(z) * dFdx(z) + dFdy(z) * dFdy(z);
                level = sqrt(level);
                level *= 50.0;
                level = min(level, 3.0);
            #else
                float level = 0.0;
            #endif
                
                for (int i = 0; i < 10; i++)
                {
                    vec2 coord = oct_to_coord(xyz_to_oct(rot_p), 512.0, 4.0);
                    vec3 c0 = convert_color(sample_texture(u_tex_base, coord, level).rgb);
                    float c1 = sample_texture(u_tex_clouds, coord, level).r;

                    c1 = c1 * c1 * 0.5 + c1 * 0.5;;
                    c.rgb += c0 * (1.0 - c1) + vec3(c1);

                    rot_p = rot(rot_p);
                }
            
                c.rgb *= 0.1;



                float thickness = 1.0;
                thickness *= thickness;
                thickness = 0.2 + 0.8 * thickness;
                
                thickness = 0.2;

                c.rgb = c.rgb * (1.0 - thickness) + vec3(0.08, 0.14, 0.3) * thickness;

                c.r = linear_to_srgb(c.r);
                c.g = linear_to_srgb(c.g);
                c.b = linear_to_srgb(c.b);

                c.rgb += noise();

                gl_FragColor = c;
            }
            `;

        let earth_frag_src =
            `        
            precision mediump float;

            uniform vec2 u_blur;
            uniform vec3 u_light_dir;
            uniform sampler2D u_tex_base;
            uniform sampler2D u_tex_clouds;
            uniform sampler2D u_tex_noise;

            varying highp vec3 pos;

            float noise() {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return n * (1.5/255.0) - 0.75/255.0;
            }
            `
            + oct_frag_src +
            `
            vec3 rot(vec3 pos){

                vec3 p = pos;
                p.x = pos.x * u_blur.x - pos.y * u_blur.y;
                p.y = pos.x * u_blur.y + pos.y * u_blur.x;
                return p;
            }

            void main(void) {
                vec4 c = vec4(0.0, 0.0, 0.0, 1.0);

                vec3 rot_p = pos;
                
                for (int i = 0; i < 10; i++)
                {
                    vec2 coord = oct_to_coord(xyz_to_oct(rot_p), 512.0, 4.0);
                    vec3 c0 = convert_color(texture2D(u_tex_base, coord).rgb);
                    float c1 = texture2D(u_tex_clouds, coord).r;

                    c1 = c1 * c1 * 0.5 + c1 * 0.5;
                    c.rgb += c0 * (1.0 - c1) + vec3(c1);

                    rot_p = rot(rot_p);
                }
            
                c.rgb *= 0.08;

                float intensity = dot(u_light_dir, pos);
                float scale = max(0.0, intensity);

                c.rgb *= scale;

                c.r = linear_to_srgb(c.r);
                c.g = linear_to_srgb(c.g);
                c.b = linear_to_srgb(c.b);

                c.rgb += noise();

                gl_FragColor = c;
            }
            `;


        let moon_simple_frag_src =
            `        
            precision mediump float;

            uniform sampler2D u_tex_base;
            uniform sampler2D u_tex_noise;

            varying highp vec3 pos;

            float noise() {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return n * (1.5/255.0) - 0.75/255.0;
            }
            `
            + oct_frag_src +
            `
            void main(void) {
                vec4 c = texture2D(u_tex_base, oct_to_coord(xyz_to_oct(pos), 512.0, 1.0));

                c.rgb = convert_color(c.rgb);

                c.r = linear_to_srgb(c.r);
                c.g = linear_to_srgb(c.g);
                c.b = linear_to_srgb(c.b);

                c.rgb += noise();

                gl_FragColor = c;
            }
            `;


        let moon_frag_src =
            `        
        precision mediump float;

        uniform vec3 u_light_dir;
        uniform sampler2D u_tex_base;
        uniform sampler2D u_tex_noise;

        varying highp vec3 pos;

        float noise() {
            float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
            return n * (1.5/255.0) - 0.75/255.0;
        }
        `
            + oct_frag_src +
            `
        void main(void) {
            vec4 c = texture2D(u_tex_base, oct_to_coord(xyz_to_oct(pos), 512.0, 1.0));


                 float intensity = dot(u_light_dir, pos);
                float scale = max(0.0, intensity);

                c.rgb *= scale;



            c.r = linear_to_srgb(c.r);
            c.g = linear_to_srgb(c.g);
            c.b = linear_to_srgb(c.b);

            c.rgb += noise();

            gl_FragColor = c;
        }
        `;

        let moon_eclipse_light_frag_src =
            `#extension GL_OES_standard_derivatives : enable

        precision highp float;

        uniform vec3 u_sun;
        uniform vec3 u_earth;
        uniform float u_progress;

        varying highp vec3 pos;

        `
            + srgb_frag_src +

            `
        void main(void) {


            float ER = 6371.0;
            float SR = 695700.0;
            float MR = 1737.4;

            vec3 p = normalize(pos) * MR;

            vec3 to_sun = -p + u_sun;
            vec3 to_earth = -p + u_earth;

            float s_sin = SR/length(to_sun);
            float s_cos = sqrt(1.0 - s_sin*s_sin);
            float sr = s_sin / s_cos;

            float e_sin = ER/length(to_earth);
            float e_cos = sqrt(1.0 - e_sin*e_sin);
            float er = e_sin / e_cos;

            float e_s_sin = clamp(length(cross(normalize(to_sun), normalize(to_earth))), 0.0, 1.0);
            float e_s_cos = sqrt(1.0 - e_s_sin * e_s_sin);
            float d = e_s_sin / e_s_cos;

            float delta = 0.25 * sqrt((-d + sr + er) * (d - sr + er) * (d + sr - er) * (d + sr + er));

            float A = sr * sr * acos((d*d + sr*sr - er*er) / (2.0 * d * sr)) +
                      er * er * acos((d*d + er*er - sr*sr) / (2.0 * d * er)) -
                      2.0 * delta;

            float f = 1.0 - clamp(A / (3.1415926535 * sr * sr), 0.0, 1.0);
            if (d < er - sr)
                f = 0.0;

            f = f * (1.0 + 300.0 * u_progress);

            f = linear_to_srgb(f);

            vec4 c = vec4(f);


            vec4 red = vec4(0.84, 0.24, 0.2, 1.0);

            float ra = smoothstep(er * 0.2, er * 0.9, d);
            c += mix(red, vec4(1.0), ra) * sqrt(u_progress);


            gl_FragColor = c;
        }
        `;



        let sun_frag_src =
            `#extension GL_OES_standard_derivatives : enable        
        precision highp float;

        uniform sampler2D u_tex_noise;

        varying highp vec3 pos;
        varying highp vec3 norm;

        float noise() {
            float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
            return n * (1.5/255.0) - 0.75/255.0;
        }


        void main(void) {

            vec3 n = normalize(norm);
            float z = max(0.0, n.z);
            float w = min(0.2,fwidth(z));
            float base_a = smoothstep(max(0.001, 0.699 - w), 0.699, z);


            float a = clamp(z/0.7, 0.0, 1.0);

            a *= a;
            a *= a;
            a *= a;
            a *= 0.7 + 0.01 * cos(pos.x * 30.0) * cos(pos.y * 30.0) * cos(pos.z * 30.0);
            a += noise();

            a = mix(a, 1.0, base_a);

            vec4 c = vec4(a);

            gl_FragColor = c;
        }
        `;

        let proto_frag_src =
            `#extension GL_OES_standard_derivatives : enable
            precision mediump float;

            varying highp vec3 pos;
            varying highp vec3 norm;

            uniform vec4 u_color;
            uniform vec4 u_params;

            float hash(float p) { p = fract(p * 0.0112); p *= p + 4.123; p *= p + p; return fract(p); }

            float noise(vec3 x) {
                const vec3 step = vec3(113.0, 144.0, 231.0);
                vec3 i = floor(x);
                vec3 f = fract(x);
                float n = dot(i, step);
                vec3 u = f * f * (3.0 - 2.0 * f);
                return mix(mix(mix(hash(n + dot(step, vec3(0, 0, 0))), hash(n + dot(step, vec3(1, 0, 0))), u.x),
                               mix(hash(n + dot(step, vec3(0, 1, 0))), hash(n + dot(step, vec3(1, 1, 0))), u.x), u.y),
                           mix(mix(hash(n + dot(step, vec3(0, 0, 1))), hash(n + dot(step, vec3(1, 0, 1))), u.x),
                               mix(hash(n + dot(step, vec3(0, 1, 1))), hash(n + dot(step, vec3(1, 1, 1))), u.x), u.y), u.z);
            }

            float fbm(vec3 x) {
                float v = 0.0;
                float a = 0.6;
                for (int i = 0; i < 5; ++i) {
                    v += a * noise(x);
                    x = x * 2.0 + 4.0;
                    a *= 0.5;
                }
                return v;
            }


            void main(void) {
                vec4 c = vec4(0.0, 0.0, 0.0, 1.0);
                
                vec3 p = pos * u_params.x;

                float a0 = fbm(p * 4.3);
                float a1 = fbm(p * 14.5 + 100.0);

                float a = 0.2 + fbm(vec3(a0 * 1.0, 4.0, a1 * 0.5) * u_params.y + u_params.z);

                a *= sqrt(norm.z);
                a = clamp(a, 0.0, 1.0);
                c.rgb = u_color.rgb * a;

                gl_FragColor = c;
            }
            `;


        let segment_vert_src =
            `
        attribute vec2 v_st;

        uniform mat4 m_mvp;
        uniform mat3 m_rot;

        uniform vec3 p0;
        uniform vec3 p1;
        uniform float r;

        varying vec3 n_dir;
        varying vec3 model_pos;

        void main(void) {
            vec3 dummy0 = vec3(0.0, 0.0, 1.0);
            vec3 dummy1 = vec3(0.7071067812, -0.7071067812, 0.0);
            
            vec3 tan = normalize(p1 - p0);

            vec3 norm = abs(dot(tan, dummy0)) > abs(dot(tan, dummy1)) ? cross(tan, dummy1) 
                                                                    : cross(tan, dummy0);
            vec3 bnorm = normalize(cross(norm, tan));

            vec3 n = norm * sin(v_st.y) + bnorm * cos(v_st.y);

            vec3 p = mix(p0, p1, v_st.x) + n * r;;

            model_pos = p;
            n_dir = m_rot * n;
            gl_Position = m_mvp * vec4(p, 1.0);
        }
        `;


        let ellipse_vert_src =
            `
            attribute vec2 v_st;

            uniform mat4 m_mvp;
            uniform mat3 m_rot;

            uniform vec4 params;

            varying float arc_length;

            void main(void) {
                float x = params.x * cos(v_st.x * params.w);
                float y = params.y * sin(v_st.x * params.w);
                float z = params.z * cos(v_st.y);

                vec2 dir = normalize(vec2(x, y));
                x += params.z * dir.x * sin(v_st.y);
                y += params.z * dir.y * sin(v_st.y);
                
                arc_length = v_st.x;

                gl_Position = m_mvp * vec4(x, y, z, 1.0);
            }
            `;

        let ellipse_frag_src =
            `
        precision mediump float;

        varying float arc_length;

        uniform vec4 color;
        uniform float normal_f;
        uniform float dashed;

        void main(void) {
            vec4 c = color;


            c *= mix (1.0, smoothstep(0.0, 0.1, cos(arc_length * 3.1415926535 * 192.0)), dashed);

            
            gl_FragColor = c;
        }
        `;

        let simple_vert_src =
            `
            attribute vec3 v_pos;

            varying vec3 pos;
                
            uniform mat4 u_mvp;

            void main(void) {       
                pos = v_pos;
                gl_Position = u_mvp * vec4(v_pos, 1.0);
            }
            `;

        let simple_frag_src =
            `
        precision mediump float;

        uniform vec4 u_color;

        void main(void) {            
            gl_FragColor = u_color;
        }
        `;


        let cone_vert_src =
            `
            attribute vec3 v_pos;
                
            uniform mat4 u_mvp;

            void main(void) {       
            
                vec3 pos = v_pos;
                pos.xy *= pos.z;
                gl_Position = u_mvp * vec4(pos, 1.0);
            }
            `;


        let cone_frag_src =
            `precision mediump float;

        uniform vec4 u_color;

        void main(void) {
            gl_FragColor = u_color;
        }
        `;



        let shadow_cone_vert_src =
            `
            attribute vec3 v_pos;

            uniform mat4 u_mvp;
            uniform float u_norm_z;

            varying vec3 pos;
            varying vec3 p0;
            varying vec3 p1;

            void main(void) {
                vec3 p = v_pos;
                p.xy *= p.z;


                vec3 n = vec3(v_pos.xy, -u_norm_z);

                vec4 pp0 = u_mvp * vec4(p, 1.0);
                vec4 pp1 = u_mvp * vec4(p + n, 1.0);
                
                pos = v_pos;
                p0 = pp0.xyz/pp0.w;
                p1 = pp1.xyz/pp1.w;

                gl_Position = pp0;
            }
            `;


        let shadow_cone_frag_src =
            `#extension GL_OES_standard_derivatives : enable
            precision mediump float;

            varying vec3 pos;
            varying vec3 p0;
            varying vec3 p1;


        uniform vec4 u_color;
        uniform vec4 u_params;

        void main(void) {
            vec4 c = u_color;

            if ((pos.z + u_params.x) * u_params.y > 0.0)
                c *= 0.0;

            gl_FragColor = c;
        }
        `;


        let color_frag_src =
            `
        precision mediump float;

        varying vec3 n_dir;
        varying vec3 model_pos;

        uniform vec4 color;
        uniform float normal_f;

        void main(void) {
            
            float f = mix(1.0, max(0.0, normalize(n_dir).z), normal_f);
            vec4 c = color;
            c.rgb *= sqrt(f);
            gl_FragColor = c;
        }
        `;

        // Based on Sébastien Hillaire's
        // "A Scalable and Production Ready Sky and Atmosphere Rendering Technique"
        // https://sebh.github.io/publications/


        let sky_preamble =
            `
        precision highp float;

        varying vec2 xy;

        float quick_sphere(vec3 r0, vec3 rd, float r2) {

        	float a = dot(rd, rd);
            vec3 s0_r0 = r0;
            float b = 2.0 * dot(rd, s0_r0);
            float c = dot(s0_r0, s0_r0) - (r2);
            float delta = b * b - 4.0*a*c;
            if (delta < 0.0 || a == 0.0)
            {
                return -1.0;
            }
            float sol0 = (-b - sqrt(delta)) / (2.0*a);
            float sol1 = (-b + sqrt(delta)) / (2.0*a);
            if (sol0 < 0.0 && sol1 < 0.0)
            {
                return -1.0;
            }
            if (sol0 < 0.0)
            {
                return max(0.0, sol1);
            }
            else if (sol1 < 0.0)
            {
                return max(0.0, sol0);
            }
            return max(0.0, min(sol0, sol1));
        }


        const vec3 rS = vec3(0.005802, 0.013558, 0.033100);

        const float mS = 0.001;
        const float mA = 0.004440;

        const vec3 oA = vec3(0.000650, 0.001881, 0.000085);
    
        const float r0 = 6371.0;
        const float r1 = 6471.0;

        const float PI = 3.141592741;
        `

        let transmittance_lut_frag_src =
            `
        
        void main(void) {            
            
            vec2 uv = xy * 0.5 + 0.5;

            float x_mu = uv.x;
            float x_r = uv.y;

            float H = sqrt(r1 * r1 - r0 * r0);
            float rho = H * x_r;
            float viewHeight = sqrt(rho * rho + r0 * r0);

            float d_min = r1 - viewHeight;
            float d_max = rho + H;
            float d = d_min + x_mu * (d_max - d_min);
            float cos_a = d == 0.0 ? 1.0 : (H * H - rho * rho - d * d) / (2.0 * viewHeight * d);
            cos_a = clamp(cos_a, -1.0, 1.0);

            vec3 pos = vec3(0.0, 0.0, viewHeight);
	        vec3 dir = vec3(0.0, sqrt(1.0 - cos_a * cos_a), cos_a);

    
            const int steps = 40;

            float dist = quick_sphere(pos, dir, r1*r1);
            float e_dist = quick_sphere(pos, dir, r0*r0);

            float step = dist * (1.0 / float(steps));

            float t = 0.0;
            vec3 optical_depth = vec3(0.0);

            for (int i = 0; i < steps; i++) {

                float altitude = length(pos) - r0;

                float rD = exp(-altitude/8.0);
                float mD = exp(-altitude/1.2);
                float oD = max(0.0, 1.0 - abs(altitude - 25.0) / 15.0);

                vec3 extinction = rS*rD + (mS + mA)*mD + oA*oD;
 
                optical_depth += extinction;

                pos += step * dir;
            }

            if (dist <= 0.0)
                optical_depth = vec3(0.0);

            vec3 transmittance = exp(-step * optical_depth);

            gl_FragColor = vec4(transmittance, 1.0);
        }
        `;

        let float_sample_src =
            linear_filtering ?
                `
        highp vec4 sample_float(sampler2D tex, highp vec2 uv, highp vec2 size) {
            return texture2D(tex, uv);
        }
        `
                :
                `
        precision highp float;
        vec4 sample_float(sampler2D tex, vec2 uv, vec2 size) {

                vec2 p = uv * size - vec2(0.5);
                vec2 p00 = floor(p);
                vec2 t = p - p00;

                vec2 st00 = (p00 + 0.5) * (1.0/size);
                vec2 st11 = (p00 + 1.5) * (1.0/size);

                vec4 c00 = texture2D(tex, vec2(st00.x, st00.y));
                vec4 c01 = texture2D(tex, vec2(st00.x, st11.y));
                vec4 c10 = texture2D(tex, vec2(st11.x, st00.y));
                vec4 c11 = texture2D(tex, vec2(st11.x, st11.y));

                vec4 c = mix(mix(c00, c10, t.x), mix(c01, c11, t.x), t.y);

            return c;
        }
        `

        let multiscatter_lut_frag_src =
            `
        uniform sampler2D u_tex;

        void main(void) {            
            
            vec2 uv = xy * 0.5 + 0.5;

            uv = (uv - 0.5/32.0) * 32.0 / 31.0;

            float c = uv.x * 2.0 - 1.0;
            float s = sqrt(1.0 - c*c);

            vec3 sun_dir = vec3(0.0, s, c);

            float h = mix(r0, r1, uv.y *0.98 + 0.01);

            vec3 multi_scat = vec3(0.0);
            vec3 L = vec3(0.0);

            for (int j = 0; j < 8; j++) {
            for (int i = 0; i < 8; i++) {

                float theta = float(i) * (2.0 * PI / 8.0);

                float phi = acos(1.0 - float(j) * (2.0 /  8.0));
                float cosPhi = cos(phi);
                float sinPhi = sin(phi);
                float cosTheta = cos(theta);
                float sinTheta = sin(theta);

                vec3 pos = vec3(0.0, 0.0, h);
                vec3 dir = vec3(cosTheta * sinPhi, sinTheta * sinPhi, cosPhi);


                const int steps = 20;

                float a_dist = quick_sphere(pos, dir, r1*r1);
                float e_dist = quick_sphere(pos, dir, r0*r0);

                float dist = 0.0;

                if (e_dist < 0.0) {
                    if (a_dist > 0.0)
                        dist = a_dist;
                } else if (a_dist > 0.0) {
                        dist = min(e_dist, a_dist);
                 }
                    
                
                float step = dist * (1.0 / float(steps));

                float t = 0.0;
                vec3 throughput = vec3(1.0);
          

                for (int i = 0; i < steps; i++) {

                    float altitude = length(pos) - r0;
                    altitude = max(0.0, altitude);

                    float rD = exp(-altitude/8.0);
                    float mD = exp(-altitude/1.2);
                    float oD = max(0.0, 1.0 - abs(altitude - 25.0) / 15.0);

                    vec3 scattering = rS*rD + mS*mD;
                    vec3 extinction = rS*rD + (mS + mA)*mD + oA*oD;
                    vec3 s_optical_depth = extinction * step;
                    vec3 s_transmittance = exp(-s_optical_depth);

                    vec3 ms_int = (scattering - scattering * s_transmittance) / extinction;

                    multi_scat += throughput * ms_int;


                    vec3 sun_transmittance = vec3(1.0);
              
                    {
                    float h = length(pos);
                    vec3 up = pos / h;
                    float cos_zenith = dot(up, sun_dir);
                    vec2 uv = vec2(0.0);
                   
                    float H = sqrt(r1*r1 - r0 * r0);
                    float rho = sqrt(max(0.0, h*h - r0 * r0));
                    float disc = h * h * (cos_zenith * cos_zenith - 1.0) + r1*r1;
                    float d = max(0.0, -h * cos_zenith + sqrt(disc));

                    float x_mu = (d - (r1 - h)) / ((rho + H) - (r1 - h));
                    float x_r = rho / H;

                    x_mu = x_mu * 255.0/256.0 + 0.5/256.0;
                    x_r = x_r * 63.0/64.0 + 0.5/64.0;
                    sun_transmittance = sample_float(u_tex, vec2(x_mu, x_r), vec2(256.0, 64.0)).rgb;
                    }

                    float phase = 1.0 / (4.0 * PI);

                    float e_dist = quick_sphere(pos, sun_dir, r0*r0);
	        	    float earthShadow = e_dist >= 0.0 ? 0.0 : 1.0;
            
                    vec3 S = earthShadow * sun_transmittance * scattering * phase;
                    vec3 Sint = (S - S * s_transmittance) / extinction;
            		
                    L += throughput * Sint;		
                    throughput *= s_transmittance;

                    pos += step * dir;
                }
            }
            }

            multi_scat *= 1.0 / (8.0 * 8.0);
            L *= 1.0 / (8.0 * 8.0);

            L *= 1.0 / (1.0 - multi_scat);
            

            gl_FragColor = vec4(L, 1.0);
        }
        `;

        let sky_lut_frag_src =
            `
        uniform sampler2D u_transmittance_tex;
        uniform sampler2D u_multi_scattering_tex;

        uniform vec3 u_sun_dir;

        vec3 agx(vec3 v) {

            const float min = -12.;
            const float max = -1.0;
            
            v = clamp(log2(v), min, max);
            v = (v - min) / (max - min);

            v  = (((((15.5 * v - 40.14) * v + 31.96) * v - 6.868) * v + 0.4298) * v + 0.1191) * v - 0.00232;
        
            return v;
        }


        void main(void) {            
            
            vec2 uv = xy * 0.5 + 0.5;
            uv = (uv - 0.5/256.0) * 256.0 / 255.0;

            float h = r0 + 0.001;

            vec3 pos = vec3(0.0, 0.0, h);
            vec3 dir;

            {

                float zenith_cos_a = mix(1.0, 0.0, uv.y * uv.y);
                float zenith_sin_a = sqrt(1.0 - zenith_cos_a * zenith_cos_a);

                float coord = uv.x;
                coord *= coord;
                float light_cos_a = -(coord*2.0 - 1.0);
                float light_sin_a = sqrt(1.0 - light_cos_a * light_cos_a);

	            dir = vec3(zenith_sin_a * light_cos_a, zenith_sin_a * light_sin_a, zenith_cos_a);
            }

	
		vec3 up = vec3(0, 0, 1);
		float sun_zenith_cos_a = dot(up, u_sun_dir);
		vec3 sun_dir = normalize(vec3(sqrt(1.0 - sun_zenith_cos_a * sun_zenith_cos_a), 0.0, sun_zenith_cos_a));
	

            const int steps = 30;

            float a_dist = quick_sphere(pos, dir, r1*r1);
            float e_dist = quick_sphere(pos, dir, r0*r0);

            float dist = 0.0;

            if (e_dist < 0.0) {
                if (a_dist > 0.0)
                    dist = a_dist;
            } else if (a_dist > 0.0) {
                    dist = min(e_dist, a_dist);
                }

              	vec3 wi = sun_dir;
	            vec3 wo = dir;
	            float cosTheta = -dot(wi, wo);

                  float g = 0.8;
                	float mie = 3.0 / (8.0 * PI) * (1.0 - g * g) / (2.0 + g * g);
	                mie *= (1.0 + cosTheta * cosTheta) / pow(1.0 + g * g - 2.0 * g * -cosTheta, 1.5);

            	    float Rayleigh = 3.0 / (16.0 * PI);
	                Rayleigh *= (1.0 + cosTheta * cosTheta);


            float step = dist * (1.0 / float(steps));

            float t = 0.0;
            vec3 throughput = vec3(1.0);
        
            vec3 L = vec3(0.0);

            for (int i = 0; i < steps; i++) {

                float altitude = length(pos) - r0;
                altitude = max(0.0, altitude);

                float rD = exp(-altitude/8.0);
                float mD = exp(-altitude/1.2);
                float oD = max(0.0, 1.0 - abs(altitude - 25.0) / 15.0);

                
                vec3 scattering = rS*rD + mS*mD;
                vec3 extinction = rS*rD + (mS + mA)*mD + oA*oD;
                vec3 s_optical_depth = extinction * step;
                vec3 s_transmittance = exp(-s_optical_depth);


                vec3 sun_transmittance = vec3(1.0);
            
                float h = length(pos);

                {
                vec3 up = pos / h;
                float cos_zenith = dot(up, sun_dir);
                vec2 uv = vec2(0.0);
                
                float H = sqrt(r1*r1 - r0 * r0);
                float rho = sqrt(max(0.0, h*h - r0 * r0));
                float disc = h * h * (cos_zenith * cos_zenith - 1.0) + r1*r1;
                float d = max(0.0, -h * cos_zenith + sqrt(disc));

                float x_mu = (d - (r1 - h)) / ((rho + H) - (r1 - h));
                float x_r = rho / H; 
                x_mu = x_mu * 255.0/256.0 + 0.5/256.0;
                x_r = x_r * 63.0/64.0 + 0.5/64.0;
                sun_transmittance = sample_float(u_transmittance_tex, vec2(x_mu, x_r), vec2(256.0, 64.0)).rgb;
                }

                float e_dist = quick_sphere(pos, sun_dir, r0*r0);
                float earthShadow = e_dist >= 0.0 ? 0.0 : 1.0;
        
                vec3 S = sun_transmittance * earthShadow * (rS*rD * Rayleigh + mS*mD * mie);

                {
                vec2 uv;
                uv.x = clamp(sun_zenith_cos_a * 0.5 + 0.5, 0.0, 1.0);
                uv.y = clamp((h - r0) / (r1 - r0), 0.0, 1.0);
                uv = uv * 31.0 / 32.0 + 0.5/32.0;

                vec3 msl = sample_float(u_multi_scattering_tex, uv, vec2(32.0, 32.0)).rgb;

                S += msl * scattering;
                }
             
                vec3 Sint = (S - S * s_transmittance) / extinction;
                
                L += throughput * Sint;		
                throughput *= s_transmittance;

                pos += step * dir;
            }
                            

            vec3 white_point = vec3(1.08241, 0.96756, 0.95003);
	        float exposure = 29.0;

            float ll = max(L.r, max(L.g, L.b));
            float a = smoothstep(0.0, 0.003, ll);
        
            L = agx(L);

            gl_FragColor = vec4(L, a);
        }
        `;



        let sky_frag_src =
            `
            precision highp float;

            uniform sampler2D u_tex_noise;
            uniform sampler2D u_tex_lut;

            uniform vec3 u_camera_pos;
            uniform vec3 u_screen_pos;
            uniform vec3 u_screen_up;
            uniform vec3 u_screen_right;
            uniform vec3 u_light_dir;

            varying vec2 xy;

            `
            + oct_frag_src +
            `
            float noise() {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return n * (1.5/255.0) - 0.75/255.0;
            }
             
            void main(void) {
                
                vec3 screen_org = u_screen_pos + xy.x * u_screen_right + xy.y * u_screen_up;
                vec3 ray_org = u_camera_pos;
                vec3 ray_dir = normalize(screen_org);

                float cos_lon = dot(normalize(u_light_dir.xy), normalize(ray_dir.xy));
                float x = -cos_lon * 0.5 + 0.5;
                x = sqrt(x);

                float cos_lat = ray_dir.z;

                float y = cos_lat;
                y = 1.0 - y;
		        y = sqrt(y);
                
                x = clamp(x, 0.0, 1.0);
                y = clamp(y, 0.0, 1.0);

                x = x * 255.0/256.0 + 0.5/256.0;
                y = y * 255.0/256.0 + 0.5/256.0;


               vec4 c = sample_float(u_tex_lut, vec2(x,y), vec2(256.0, 64.0));


               c.rgb += noise();

                if (cos_lat < 0.0)
                    c = vec4(0.0);

                gl_FragColor = c;
            }
            `;


        let earth_sky_frag_src =
            `
            precision highp float;

            uniform sampler2D u_tex_noise;
            uniform sampler2D u_transmittance_tex;

            uniform vec3 u_light_dir;
            uniform vec3 u_view_dir;
            uniform float u_h;

            varying highp vec3 pos;

            float noise() {
                float n = texture2D(u_tex_noise, vec2(gl_FragCoord * 1.0/32.0)).r;
                return n * (1.5/255.0) - 0.75/255.0;
            }

            float linear_to_srgb(float c) {
                return c < 0.0031308 ? 12.92 * c : 1.055 * pow(c, 1.0/2.4) - 0.055;
            }
                            
            void main(void) {

                 float h = r1 - 2.0;

                vec3 up = normalize(pos);
                vec3 hit = up * h;


                vec3 p = hit;

            vec3 dir = -u_view_dir;
		vec3 sun_dir = u_light_dir;
	

            const int steps = 30;

            float a_dist = quick_sphere(p, dir, r1*r1);
            float e_dist = quick_sphere(p, dir, r0*r0);

            float dist = 0.0;

            if (e_dist < 0.0) {
                if (a_dist > 0.0)
                    dist = a_dist;
            } else if (a_dist > 0.0) {
                    dist = min(e_dist, a_dist);
                }

              	vec3 wi = sun_dir;
	            vec3 wo = dir;
	            float cosTheta = -dot(wi, wo);

                  float g = 0.8;
                	float mie = 3.0 / (8.0 * PI) * (1.0 - g * g) / (2.0 + g * g);
	                mie *= (1.0 + cosTheta * cosTheta) / pow(1.0 + g * g - 2.0 * g * -cosTheta, 1.5);

            	    float Rayleigh = 3.0 / (16.0 * PI);
	                Rayleigh *= (1.0 + cosTheta * cosTheta);


                
            float step = dist * (1.0 / float(steps));

            float t = 0.0;
            vec3 throughput = vec3(1.0);
        
            vec3 L = vec3(0.0);

            for (int i = 0; i < steps; i++) {

                float altitude = length(p) - r0;
                altitude = max(0.0, altitude);

                float rD = exp(-altitude/8.0);
                float mD = exp(-altitude/1.2);
                float oD = max(0.0, 1.0 - abs(altitude - 25.0) / 15.0);

                
                vec3 scattering = rS*rD + mS*mD;
                vec3 extinction = rS*rD + (mS + mA)*mD + oA*oD;
                vec3 s_optical_depth = extinction * step;
                vec3 s_transmittance = exp(-s_optical_depth);


                vec3 sun_transmittance = vec3(1.0);
            
                float h = length(p);

                {
                vec3 up = p / h;
                float cos_zenith = dot(up, sun_dir);
                vec2 uv = vec2(0.0);
                
                float H = sqrt(r1*r1 - r0 * r0);
                float rho = sqrt(max(0.0, h*h - r0 * r0));
                float disc = h * h * (cos_zenith * cos_zenith - 1.0) + r1*r1;
                float d = max(0.0, -h * cos_zenith + sqrt(disc));

                float x_mu = (d - (r1 - h)) / ((rho + H) - (r1 - h));
                float x_r = rho / H;

                   x_mu = x_mu * 255.0/256.0 + 0.5/256.0;
                    x_r = x_r * 63.0/64.0 + 0.5/64.0;
                sun_transmittance = sample_float(u_transmittance_tex, vec2(x_mu, x_r), vec2(256.0, 64.0)).rgb;
                
                }

              

                float e_dist = quick_sphere(p, sun_dir, r0*r0);
                float earthShadow = e_dist >= 0.0 ? 0.0 : 1.0;
            

                vec3 S = sun_transmittance * earthShadow;
                S *= (rS*rD * Rayleigh + mS*mD * mie);

                    
                vec3 Sint = (S - S * s_transmittance) / extinction;
                
                L += throughput * Sint;		
                throughput *= s_transmittance;

                p += step * dir;
            }

                vec3 color = 5.0 * L;

                color.r = linear_to_srgb(color.r);
                color.g = linear_to_srgb(color.g);
                color.b = linear_to_srgb(color.b);

                color.rgb += noise();

                gl_FragColor = vec4(color, 0.0);
            }
            `;

        let em_radial_shader_frag_src = `
            precision highp float;

            varying vec2 xy;

            uniform sampler2D u_tex_noise;

            uniform vec4 u_dir0;
            uniform vec4 u_dir1;
            uniform vec4 u_dir2;
            uniform vec4 u_dir3;
            uniform vec4 u_p0;
            uniform vec4 u_p1;
            uniform vec4 u_p2;
            uniform vec4 u_p3;
            uniform vec4 u_params;


            float amp(float l, float phase) {
                float t = u_params.y;
                float f = u_params.x;

                float arg = f * l - t + phase;

                float a = sin(arg);

                float a0 = clamp(3.0 * sin(arg * 0.25), 0.0, 1.0);
                float a1 = smoothstep(-0.5, -0.4, arg * u_params.w) - smoothstep(0.4, 0.5, arg * u_params.w);

                if (u_params.z == 0.0)
                    a *= a0;
                else if (u_params.z == 1.0)
                    a *= a1;

                return a;
            }
            void main(void) {

                float l0 = length(xy - u_p0.xy);
                float l1 = length(xy - u_p1.xy);
                float l2 = length(xy - u_p2.xy);
                float l3 = length(xy - u_p3.xy);
                
                float a = 0.0;

                a += u_p0.z * amp(l0, u_p0.w) * (1.0 / (l0+0.3));
                a += u_p1.z * amp(l1, u_p1.w) * (1.0 / (l1+0.3));
                a += u_p2.z * amp(l2, u_p2.w) * (1.0 / (l2+0.3));
                a += u_p3.z * amp(l3, u_p3.w) * (1.0 / (l3+0.3));

                a += u_dir0.z * amp(dot(u_dir0.xy, xy), u_dir0.w);
                a += u_dir1.z * amp(dot(u_dir1.xy, xy), u_dir1.w);
                a += u_dir2.z * amp(dot(u_dir2.xy, xy), u_dir2.w);
                a += u_dir3.z * amp(dot(u_dir3.xy, xy), u_dir3.w);

                vec4 c = a > 0.0 ? vec4(0.89,0.21,0.14,1) : vec4(0.0,0.56,1.0,1);
           
                c *= abs(a);

                gl_FragColor = c;
            }
        `;


        ///


        let color_fill_shader;
        let lambert_sphere_shader;
        let hapke_sphere_shader;
        let blob_shader;
        let land_shader;
        let mesh_shader;
        let trail_shader;
        let disc_shader;
        let shaded_mesh_shader;
        let plain_sphere_shader;
        let hemi_sphere_shader;
        let shaded_sphere_shader;
        let sun_eclipse_shader;
        let parted_sphere_shader;
        let earth_simple_shader;
        let earth_sdf_shader;
        let earth_sdf_eclipse_light_shader;
        let earth_shader;
        let moon_simple_shader;
        let moon_shader;
        let moon_eclipse_light_shader;
        let sun_shader;
        let proto_shader;
        let tidal_water_shader;
        let tetra_shader;
        let tetra_prism_shader;
        let star_shader;
        let segment_shader;
        let cone_shader;
        let shadow_cone_shader;
        let ellipse_shader;
        let sun_rays_shader;
        let complex_moon_shader;
        let elevation_moon_shader;

        let eclipse_shader;

        let transmittance_lut_shader;
        let multiscatter_lut_shader;

        let sky_lut_shader;
        let sky_shader;

        let earth_sky_shader;

        let em_radial_shader;

        ///

        earth_sdf_eclipse_light_shader = new Shader(gl,
            sphere_vert_src,
            earth_sdf_eclipse_light_frag_src,
            ["v_pos"],
            ["u_mvp", "u_rot", "u_tex_base", "u_sun", "u_moon"]);




        segment_shader = new Shader(gl,
            segment_vert_src,
            color_frag_src, ["v_st"], ["m_mvp", "m_rot", "p0", "p1", "r", "color", "normal_f"]);

        cone_shader = new Shader(gl,
            cone_vert_src,
            cone_frag_src, ["v_pos"], ["u_mvp", "u_color"]);

        parted_sphere_shader = new Shader(gl,
            parted_sphere_vert_src,
            parted_sphere_frag_src,
            ["v_pos"],
            ["u_mvp", "u_rot", "u_spread", "u_color"]);



        earth_sdf_shader = new Shader(gl,
            sphere_vert_src,
            earth_sdf_frag_src,
            ["v_pos"],
            ["u_mvp", "u_rot", "u_tex_base", "u_clear"]);


        shaded_sphere_shader = new Shader(gl,
            sphere_vert_src,
            shaded_sphere_frag_src,
            ["v_pos"],
            ["u_mvp", "u_rot", "u_color"]);

        plain_sphere_shader = new Shader(gl,
            plain_sphere_vert_src,
            plain_sphere_frag_src,
            ["v_pos"],
            ["u_mvp", "u_rot", "u_color"]);

        hemi_sphere_shader = new Shader(gl,
            hemi_sphere_vert_src,
            hemi_sphere_frag_src,
            ["v_pos"],
            ["u_mvp", "u_rot", "u_color"]);


        ellipse_shader = new Shader(gl,
            ellipse_vert_src,
            ellipse_frag_src, ["v_st"], ["m_mvp", "m_rot", "dashed", "params", "color", "normal_f"]);


        if (!mini) {


            color_fill_shader = new Shader(gl,
                full_screen_vert_src,
                color_fill_frag_src,
                ["v_position"],
                ["u_color"]);


            lambert_sphere_shader = new Shader(gl,
                full_screen_vert_src,
                preamble_src + lambert_cosine_brdf + brdf_sphere_frag_src,
                ["v_position"],
                ["u_tex_noise", "u_camera_pos", "u_screen_pos", "u_screen_up", "u_screen_right", "u_light_dir", "u_marker",
                ]);

            hapke_sphere_shader = new Shader(gl,
                full_screen_vert_src,
                preamble_src + hapke_cosine_brdf + brdf_sphere_frag_src,
                ["v_position"],
                ["u_tex_noise", "u_camera_pos", "u_screen_pos", "u_screen_up", "u_screen_right", "u_light_dir", "u_marker",
                ]);

            blob_shader = new Shader(gl,
                blob_vert_src,
                blob_frag_src,
                ["v_pos", "v_id"],
                ["u_mvp", "u_size", "u_n_threshold", "u_color0", "u_color1"]);


            land_shader = new Shader(gl,
                land_vert_src,
                land_frag_src,
                ["v_pos"],
                ["u_mvp", "u_color", "u_seed", "u_tex_noise"]);

            mesh_shader = new Shader(gl,
                mesh_vert_src,
                mesh_frag_src,
                ["v_pos"],
                ["u_mvp", "u_params"]);

            trail_shader = new Shader(gl,
                trail_vert_src,
                trail_frag_src,
                ["v_pos", "v_p0", "v_p1", "v_id"],
                ["u_mvp", "u_rot", "u_offset", "u_params", "u_color", "u_alpha_range"]);

            disc_shader = new Shader(gl,
                quad_vert_src,
                disc_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_color", "u_feather", "u_coords"]);

            shaded_mesh_shader = new Shader(gl,
                shaded_mesh_vert_src,
                shaded_mesh_frag_src,
                ["v_pos", "v_norm", "v_shade"],
                ["u_mvp", "u_rot", "u_color"]);


            sun_eclipse_shader = new Shader(gl,
                sphere_vert_src,
                sun_eclipse_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_tex_noise", "u_dir0", "u_dir1", "u_dir2", "u_dim"]);


            earth_simple_shader = new Shader(gl,
                sphere_vert_src,
                sample_tex_preamble + srgb_tex_preamble + srgb_frag_src + earth_simple_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_tex_base", "u_tex_clouds", "u_tex_noise", "u_blur"]);


            earth_shader = new Shader(gl,
                sphere_vert_src,
                srgb_tex_preamble + srgb_frag_src + earth_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_light_dir", "u_tex_base", "u_tex_clouds", "u_tex_noise", "u_blur"]);



            moon_simple_shader = new Shader(gl,
                sphere_vert_src,
                srgb_tex_preamble + srgb_frag_src + moon_simple_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", , "u_tex_base", "u_tex_noise"]);

            moon_shader = new Shader(gl,
                sphere_vert_src,
                srgb_tex_preamble + srgb_frag_src + moon_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_light_dir", "u_tex_base", "u_tex_noise"]);


            moon_eclipse_light_shader = new Shader(gl,
                sphere_vert_src,
                moon_eclipse_light_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_sun", "u_earth", "u_progress"]);

            sun_shader = new Shader(gl,
                sphere_vert_src,
                srgb_tex_preamble + sun_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_tex_noise"]);


            proto_shader = new Shader(gl,
                sphere_vert_src,
                proto_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_color", "u_params"]);

            tidal_water_shader = new Shader(gl,
                tidal_water_vert_src,
                tidal_water_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_p0", "u_p1", "u_params", "u_color"]);

            tetra_shader = new Shader(gl,
                tetra_vert_src,
                tetra_frag_src,
                ["v_pos0", "v_pos1", "v_pos2", "v_pos3", "v_weight", "v_n_weight"],
                ["u_mvp", "u_rot", "u_light_dir"]);

            tetra_prism_shader = new Shader(gl,
                tetra_prism_vert_src,
                tetra_prism_frag_src,
                ["v_pos0", "v_pos1", "v_pos2", "v_pos3", "v_weight", "v_n_weight"],
                ["u_mvp", "u_rot", "u_light_dir"]);


            star_shader = new Shader(gl,
                star_vert_src,
                star_frag_src,
                ["v_xyzm"],
                ["u_mvp"]);

            shadow_cone_shader = new Shader(gl,
                shadow_cone_vert_src,
                shadow_cone_frag_src, ["v_pos"], ["u_mvp", "u_norm_z", "u_color", "u_params"]);

            sun_rays_shader = new Shader(gl,
                transformed_vert_src,
                sun_rays_frag_src,
                ["v_pos"],
                ["u_mat", "u_color", "u_seed"]);

            complex_moon_shader = new Shader(gl,
                transformed_vert_src,
                derivatives_preamble + srgb_tex_preamble + complex_moon_frag_src,
                ["v_position"],
                ["u_mat", "camera_pos", "screen_pos", "screen_up", "screen_right", "light_dir", "earthlight", "screen_diff", "dxdy", "sky_dir", "tint",
                    "tex_color", "tex_height", "tex_sky"]);

            elevation_moon_shader = new Shader(gl,
                transformed_vert_src,
                elevation_moon_frag_src,
                ["v_position"],
                ["u_mat", "camera_pos", "screen_pos", "screen_up", "screen_right", "light_dir", "screen_diff", "dxdy",
                    "u_height_scale", "tex_color", "tex_height"]);

            eclipse_shader = new Shader(gl,
                centered_vert_src,
                eclipse_frag_src,
                ["v_position"],
                []);

            transmittance_lut_shader = new Shader(gl,
                full_screen_vert_src,
                sky_preamble + transmittance_lut_frag_src,
                ["v_position"],
                []);

            multiscatter_lut_shader = new Shader(gl,
                full_screen_vert_src,
                sky_preamble + float_sample_src + multiscatter_lut_frag_src,
                ["v_position"],
                ["u_tex"]);

            sky_lut_shader = new Shader(gl,
                full_screen_vert_src,
                sky_preamble + float_sample_src + sky_lut_frag_src,
                ["v_position"],
                ["u_transmittance_tex", "u_multi_scattering_tex", "u_sun_dir", "u_h"]);


            sky_shader = new Shader(gl,
                full_screen_vert_src,
                float_sample_src + sky_frag_src,
                ["v_position"],
                ["u_tex_noise", "u_tex_lut", "u_camera_pos", "u_screen_pos", "u_screen_up", "u_screen_right", "u_light_dir",
                ]);

            earth_sky_shader = new Shader(gl,
                sphere_vert_src,
                sky_preamble + float_sample_src + earth_sky_frag_src,
                ["v_pos"],
                ["u_mvp", "u_rot", "u_light_dir", "u_view_dir", "u_h", "u_transmittance_tex", "u_tex_noise"]);



            em_radial_shader = new Shader(gl,
                full_screen_vert_src,
                em_radial_shader_frag_src,
                ["v_position"],
                ["u_tex_noise", "u_dir0", "u_dir1", "u_dir2", "u_dir3", "u_p0", "u_p1", "u_p2", "u_p3", "u_params"]);


        }

        let prev_width, prev_height;

        let viewport_w = 0;
        let viewport_h = 0;


        this.create_render_target = function (w, h, float, params = []) {

            let framebuffer = gl.createFramebuffer();
            let texture = gl.createTexture();

            gl.bindFramebuffer(gl.FRAMEBUFFER, framebuffer);
            gl.bindTexture(gl.TEXTURE_2D, texture);

            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
            gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

            for (let param of params) {
                gl.texParameteri(gl.TEXTURE_2D, param[0], param[1]);
            }

            let type = float ? (half_float_ext ? half_float_ext.HALF_FLOAT_OES : gl.FLOAT) : gl.UNSIGNED_BYTE;

            gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, w, h, 0, gl.RGBA, type, null);

            gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, texture, 0);

            gl.bindFramebuffer(gl.FRAMEBUFFER, null);
            gl.bindTexture(gl.TEXTURE_2D, null);

            return { framebuffer: framebuffer, texture: texture, width: w, height: h };
        }



        this.begin = function (width, height) {

            width *= scale;
            height *= scale;

            if (width != prev_width || height != prev_height) {
                canvas.width = width;
                canvas.height = height;
                prev_width = width;
                prev_height = height;
            }

            gl.viewport(0, 0, width, height);

            gl.disable(gl.BLEND);
            gl.depthMask(true);
            gl.depthFunc(gl.LEQUAL);
            gl.disable(gl.DEPTH_TEST);
            gl.disable(gl.STENCIL_TEST);
            gl.disable(gl.SCISSOR_TEST);

            gl.clearColor(0, 0, 0, 0);
            gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT | gl.STENCIL_BUFFER_BIT);

            gl.disable(gl.CULL_FACE);



            gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA);

            viewport_w = Math.round(width);
            viewport_h = Math.round(height);
        }

        let transmittance_texture;
        let multiscatter_texture;

        let sky_lut_target;

        this.create_transmittance_lut = function () {

            if (transmittance_texture)
                return;

            let target = this.create_render_target(256, 64, true, [
                [gl.TEXTURE_MIN_FILTER, linear_filtering ? gl.LINEAR : gl.NEAREST],
                [gl.TEXTURE_MAG_FILTER, linear_filtering ? gl.LINEAR : gl.NEAREST],
            ]);

            this.push_render_target(target);

            this.draw_full("transmittance_lut");

            this.pop_render_target();

            transmittance_texture = target.texture;

            {
                let target = this.create_render_target(32, 32, true, [
                    [gl.TEXTURE_MIN_FILTER, linear_filtering ? gl.LINEAR : gl.NEAREST],
                    [gl.TEXTURE_MAG_FILTER, linear_filtering ? gl.LINEAR : gl.NEAREST],
                ])

                this.push_render_target(target);

                this.draw_full("multiscatter_lut");

                this.pop_render_target();

                multiscatter_texture = target.texture;
            }

            sky_lut_target = this.create_render_target(256, 256, true, [
                [gl.TEXTURE_MIN_FILTER, linear_filtering ? gl.LINEAR : gl.NEAREST],
                [gl.TEXTURE_MAG_FILTER, linear_filtering ? gl.LINEAR : gl.NEAREST],
                [gl.TEXTURE_WRAP_S, gl.MIRRORED_REPEAT],
                [gl.TEXTURE_WRAP_T, gl.MIRRORED_REPEAT],
            ])

        }

        this.update_sky_lut_texture = function (sun_dir, h) {
            this.push_render_target(sky_lut_target);

            this.draw_full("sky_lut", { sun_dir: sun_dir, h: h });

            this.pop_render_target();
        }

        this.push_render_target = function (render_target) {
            gl.bindFramebuffer(gl.FRAMEBUFFER, render_target.framebuffer);
            gl.viewport(0, 0, render_target.width, render_target.height);

            gl.clearColor(0.0, 0.0, 0.0, 0.0);
            gl.clear(gl.COLOR_BUFFER_BIT);
        }

        this.pop_render_target = function () {
            gl.bindFramebuffer(gl.FRAMEBUFFER, null);
        }


        this.viewport = function (x, y, w, h) {
            gl.viewport(x * scale, y * scale, w * scale, h * scale);
        }

        this.scissors = function (x, y, w, h) {

            gl.enable(gl.SCISSOR_TEST);

            gl.scissor(x * scale, y * scale, w * scale, h * scale);
        }

        this.set_blend_enabled = function (x) {
            if (x)
                gl.enable(gl.BLEND);
            else
                gl.disable(gl.BLEND);
        }

        this.set_depth_write_enabled = function (x) {
            gl.depthMask(x);
        }

        this.set_depth_fail_enabled = function (x) {
            gl.depthFunc(x ? gl.GREATER : gl.LEQUAL);
        }

        this.set_color_write_enabled = function (x) {
            gl.colorMask(x, x, x, x);
        }

        this.set_depth_test_enabled = function (x) {
            if (x)
                gl.enable(gl.DEPTH_TEST);
            else
                gl.disable(gl.DEPTH_TEST);
        }


        this.set_cull_face_enabled = function (x) {
            if (x)
                gl.enable(gl.CULL_FACE);
            else
                gl.disable(gl.CULL_FACE);
        }

        this.set_stencil_test_enabled = function (x) {
            if (x)
                gl.enable(gl.STENCIL_TEST);
            else
                gl.disable(gl.STENCIL_TEST);
        }

        this.set_blend_mode = function (x) {
            if (x === "sover")
                gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA);
            else if (x === "dover")
                gl.blendFunc(gl.ONE_MINUS_DST_ALPHA, gl.ONE);
            else if (x === "plusl")
                gl.blendFunc(gl.ONE, gl.ONE);
            else if (x === "multiply")
                gl.blendFunc(gl.ZERO, gl.SRC_COLOR);
        }

        this.set_shadow_geometry_stencil_pass = function () {

            gl.disable(gl.CULL_FACE);
            gl.enable(gl.STENCIL_TEST);
            gl.depthMask(false);
            gl.colorMask(false, false, false, false);

            gl.stencilFunc(gl.ALWAYS, 0, 0xFF);

            gl.stencilOpSeparate(gl.FRONT, gl.KEEP, gl.KEEP, gl.INCR_WRAP);
            gl.stencilOpSeparate(gl.BACK, gl.KEEP, gl.KEEP, gl.DECR_WRAP);
        }

        this.start_shadow_tint_pass = function () {
            gl.colorMask(true, true, true, true);
            gl.enable(gl.BLEND);
            gl.blendFunc(gl.DST_ALPHA, gl.ZERO);
            gl.stencilFunc(gl.NOTEQUAL, 0, 0xFF);
            gl.stencilOpSeparate(gl.FRONT_AND_BACK, gl.KEEP, gl.KEEP, gl.KEEP);
        }

        this.end_shadow_tint_pass = function () {
            gl.disable(gl.BLEND);
            gl.depthMask(true);

            gl.disable(gl.STENCIL_TEST);
        }


        this.draw_stars = function (mvp) {

            if (!eph)
                return;

            let n = eph.star_count;

            let shader = star_shader;
            gl.useProgram(shader.shader);


            gl.bindBuffer(gl.ARRAY_BUFFER, star_buffer);

            if (!copied_star_data) {
                let b = new Float32Array(9110 * 4);
                let d = eph.star_data;
                for (let i = 0; i < n; i++) {
                    b[i * 4 + 0] = cos(d[i * 3]) * cos(d[i * 3 + 1]);
                    b[i * 4 + 1] = sin(d[i * 3]) * cos(d[i * 3 + 1]);
                    b[i * 4 + 2] = sin(d[i * 3 + 1]);
                    b[i * 4 + 3] = d[i * 3 + 2];
                }
                gl.bufferData(gl.ARRAY_BUFFER, b, gl.STATIC_DRAW);
                copied_star_data = true;
            }

            gl.enableVertexAttribArray(shader.attributes["v_xyzm"]);
            gl.vertexAttribPointer(shader.attributes["v_xyzm"], 4, gl.FLOAT, false, 4 * float_size, 0);

            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));

            gl.drawArrays(gl.POINTS, 0, n);
        }




        this.finish = function () {
            gl.flush();
            return gl.canvas;
        }

        this.update_blob_buffer = function (buffer) {
            gl.bindBuffer(gl.ARRAY_BUFFER, blob_buffer);
            gl.bufferSubData(gl.ARRAY_BUFFER, 0, buffer);
        }

        this.draw_blobs = function (mvp, count, params) {

            let shader = blob_shader;

            gl.useProgram(shader.shader);


            gl.bindBuffer(gl.ARRAY_BUFFER, blob_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_pos"]);
            gl.vertexAttribPointer(shader.attributes["v_pos"], 2, gl.FLOAT, false, 2 * float_size, 0);


            gl.bindBuffer(gl.ARRAY_BUFFER, instance_id_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_id"]);
            gl.vertexAttribPointer(shader.attributes["v_id"], 1, gl.FLOAT, false, float_size, 0);



            gl.uniform1f(shader.uniforms["u_size"], params.size);
            gl.uniform1f(shader.uniforms["u_n_threshold"], params.n_threshold);
            gl.uniform4fv(shader.uniforms["u_color0"], params.color0);
            gl.uniform4fv(shader.uniforms["u_color1"], params.color1);


            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));

            gl.drawArrays(gl.POINTS, 0, count);
        }

        this.draw_mesh = function (mvp, params) {

            let shader = mesh_shader;

            gl.useProgram(shader.shader);

            gl.bindBuffer(gl.ARRAY_BUFFER, mesh_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_pos"]);
            gl.vertexAttribPointer(shader.attributes["v_pos"], 2, gl.FLOAT, false, 2 * float_size, 0);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, mesh_index_buffer);


            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));
            gl.uniform4fv(shader.uniforms["u_params"], params);


            gl.drawElements(gl.TRIANGLES, (mesh_size - 1) * (mesh_size - 1) * 3 * 2, gl.UNSIGNED_SHORT, 0);
        }

        this.draw_horizon = function (mvp, params) {

            let shader = land_shader;

            gl.useProgram(shader.shader);

            gl.bindBuffer(gl.ARRAY_BUFFER, mesh_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_pos"]);
            gl.vertexAttribPointer(shader.attributes["v_pos"], 2, gl.FLOAT, false, 2 * float_size, 0);

            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, mesh_index_buffer);

            gl.activeTexture(gl.TEXTURE0);
            gl.bindTexture(gl.TEXTURE_2D, textures["noise"]);

            gl.uniform1i(shader.uniforms["u_tex_noise"], 0);


            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));
            gl.uniform4fv(shader.uniforms["u_color"], params.color);
            gl.uniform2fv(shader.uniforms["u_seed"], params.seed);


            gl.drawElements(gl.TRIANGLES, (mesh_size - 1) * (mesh_size - 1) * 3 * 2, gl.UNSIGNED_SHORT, 0);
        }

        this.draw_full = function (mode, params) {

            let shader;
            let hex = false;

            if (mode === "lambert_sphere") {
                shader = lambert_sphere_shader;
            } else if (mode === "hapke_sphere") {
                shader = hapke_sphere_shader;
            } else if (mode === "color_fill") {
                shader = color_fill_shader;
            } else if (mode === "complex_moon") {
                shader = complex_moon_shader;
                hex = true;
            } else if (mode === "sun_rays") {
                shader = sun_rays_shader;
                hex = true;
            } else if (mode === "elevation_moon") {
                shader = elevation_moon_shader;
                hex = true;
            } else if (mode === "eclipse") {
                shader = eclipse_shader;
            } else if (mode === "transmittance_lut") {
                shader = transmittance_lut_shader;
            } else if (mode === "multiscatter_lut") {
                shader = multiscatter_lut_shader;
            } else if (mode === "sky_lut") {
                shader = sky_lut_shader;
            } else if (mode === "sky") {
                shader = sky_shader;
            } else if (mode === "em_radial") {
                shader = em_radial_shader;
            }

            gl.useProgram(shader.shader);

            if (hex) {
                gl.bindBuffer(gl.ARRAY_BUFFER, hexagon_vertex_buffer);
                gl.uniform4fv(shader.uniforms["u_mat"], params.mat || [1, 1, 0, 0]);
            }
            else {
                gl.bindBuffer(gl.ARRAY_BUFFER, full_screen_vertex_buffer);
            }

            gl.enableVertexAttribArray(shader.attributes["v_position"]);
            gl.vertexAttribPointer(shader.attributes["v_position"], 2, gl.FLOAT, false, 0, 0);


            if (mode === "lambert_sphere" || mode === "hapke_sphere" || mode === "sky") {

                gl.activeTexture(gl.TEXTURE0);
                gl.bindTexture(gl.TEXTURE_2D, textures["noise"]);

                gl.uniform1i(shader.uniforms["u_tex_noise"], 0);

                gl.uniform3fv(shader.uniforms["u_camera_pos"], params.camera_pos);
                gl.uniform3fv(shader.uniforms["u_screen_pos"], vec_sub(params.screen_pos, params.camera_pos));
                gl.uniform3fv(shader.uniforms["u_screen_up"], params.screen_up);
                gl.uniform3fv(shader.uniforms["u_screen_right"], params.screen_right);
                gl.uniform3fv(shader.uniforms["u_light_dir"], params.light_dir);

                if (mode === "sky") {

                    gl.activeTexture(gl.TEXTURE1);
                    gl.bindTexture(gl.TEXTURE_2D, sky_lut_target.texture);
                    gl.uniform1i(shader.uniforms["u_tex_lut"], 1);
                } else {
                    gl.uniform1f(shader.uniforms["u_marker"], params.marker);
                }
            } else if (mode === "em_radial") {

                gl.uniform4fv(shader.uniforms["u_dir0"], params.dir0);
                gl.uniform4fv(shader.uniforms["u_dir1"], params.dir1);
                gl.uniform4fv(shader.uniforms["u_dir2"], params.dir2);
                gl.uniform4fv(shader.uniforms["u_dir3"], params.dir3);
                gl.uniform4fv(shader.uniforms["u_p0"], params.p0);
                gl.uniform4fv(shader.uniforms["u_p1"], params.p1);
                gl.uniform4fv(shader.uniforms["u_p2"], params.p2);
                gl.uniform4fv(shader.uniforms["u_p3"], params.p3);
                gl.uniform4fv(shader.uniforms["u_params"], params.params);


                gl.activeTexture(gl.TEXTURE0);
                gl.bindTexture(gl.TEXTURE_2D, textures["noise"]);
                gl.uniform1i(shader.uniforms["u_tex_noise"], 0);
            } else if (mode === "multiscatter_lut") {

                gl.activeTexture(gl.TEXTURE0);
                gl.bindTexture(gl.TEXTURE_2D, transmittance_texture);

                gl.uniform1i(shader.uniforms["u_tex"], 0);
            } else if (mode === "sky_lut") {

                gl.activeTexture(gl.TEXTURE0);
                gl.bindTexture(gl.TEXTURE_2D, transmittance_texture);
                gl.uniform1i(shader.uniforms["u_transmittance_tex"], 0);

                gl.activeTexture(gl.TEXTURE1);
                gl.bindTexture(gl.TEXTURE_2D, multiscatter_texture);
                gl.uniform1i(shader.uniforms["u_multi_scattering_tex"], 1);

                gl.uniform1f(shader.uniforms["u_h"], params.h);
                gl.uniform3fv(shader.uniforms["u_sun_dir"], params.sun_dir);

            } else if (mode === "color_fill") {
                gl.uniform4fv(shader.uniforms["u_color"], params.color);
            } else if (mode === "color_fill" || mode === "sun_rays") {
                gl.uniform4fv(shader.uniforms["u_color"], params.color);
                gl.uniform1f(shader.uniforms["u_seed"], params.seed);
            } else if (mode === "complex_moon" || mode === "elevation_moon") {


                gl.activeTexture(gl.TEXTURE1);
                gl.bindTexture(gl.TEXTURE_2D, textures["moon_height_map"]);

                gl.uniform3fv(shader.uniforms["camera_pos"], params.camera_pos);
                gl.uniform3fv(shader.uniforms["screen_pos"], params.screen_pos);
                gl.uniform3fv(shader.uniforms["screen_up"], params.screen_up);
                gl.uniform3fv(shader.uniforms["screen_right"], params.screen_right);

                if (mode === "complex_moon") {
                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["moon_color"]);
                    gl.uniform1i(shader.uniforms["tex_color"], 0);

                    if (params.sky_dir) {
                        gl.activeTexture(gl.TEXTURE2);
                        gl.bindTexture(gl.TEXTURE_2D, sky_lut_target.texture);
                        gl.uniform1i(shader.uniforms["tex_sky"], 2);

                        gl.uniform3fv(shader.uniforms["sky_dir"], params.sky_dir);
                    } else {
                        gl.uniform3fv(shader.uniforms["sky_dir"], [-1, -1, -1]);
                    }

                    gl.uniform4fv(shader.uniforms["tint"], params.tint || [1, 1, 1, 1]);

                    gl.uniform4fv(shader.uniforms["light_dir"], params.light_dir);
                    gl.uniform1f(shader.uniforms["earthlight"], params.earthlight || 0);
                } else {
                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, elevation_lut_texture);
                    gl.uniform1i(shader.uniforms["tex_color"], 0);

                    gl.uniform2fv(shader.uniforms["u_height_scale"], params.height_scale);
                }


                gl.uniform3fv(shader.uniforms["screen_diff"], vec_sub(params.screen_pos, params.camera_pos));
                gl.uniform2fv(shader.uniforms["dxdy"], [0.5 / viewport_w, 0.5 / viewport_h]);

                gl.uniform1i(shader.uniforms["tex_height"], 1);
            }

            gl.drawArrays(gl.TRIANGLES, 0, hex ? 12 : 3);
        }

        this.update_trail_buffer = function (buffer) {
            gl.bindBuffer(gl.ARRAY_BUFFER, history_trail_buffer);
            gl.bufferSubData(gl.ARRAY_BUFFER, 0, buffer);
        }

        this.draw_trail = function (mvp, rot, offset, count, params) {

            let shader = trail_shader;

            gl.useProgram(shader.shader);

            let attrib_names = ["v_p0", "v_p1"];

            gl.bindBuffer(gl.ARRAY_BUFFER, history_trail_buffer);

            for (let i = 0; i < attrib_names.length; i++) {
                let loc = shader.attributes[attrib_names[i]];
                gl.enableVertexAttribArray(loc);
                gl.vertexAttribPointer(loc, 3, gl.FLOAT, false, 3 * float_size, (i * 3 + offset) * float_size);
                inst_ext.vertexAttribDivisorANGLE(loc, 1);
            }

            gl.bindBuffer(gl.ARRAY_BUFFER, instance_id_buffer);

            const id_loc = shader.attributes["v_id"];
            gl.enableVertexAttribArray(id_loc);
            gl.vertexAttribPointer(id_loc, 1, gl.FLOAT, false, float_size, 0);
            inst_ext.vertexAttribDivisorANGLE(id_loc, 1);


            gl.bindBuffer(gl.ARRAY_BUFFER, quad_vertex_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_pos"]);
            gl.vertexAttribPointer(shader.attributes["v_pos"], 2, gl.FLOAT, false, 2 * float_size, 0);



            gl.uniform4fv(shader.uniforms["u_color"], params.color);

            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));
            gl.uniformMatrix3fv(shader.uniforms["u_rot"], false, mat3_invert(rot));

            gl.uniform2fv(shader.uniforms["u_params"], params.params || [0.003, 1]);
            gl.uniform3fv(shader.uniforms["u_offset"], params.offset || [0, 0, 0]);
            gl.uniform4fv(shader.uniforms["u_alpha_range"], params.alpha_range || [0, 100.0, 1e6, 1e7]);


            inst_ext.drawArraysInstancedANGLE(gl.TRIANGLE_STRIP, 0, 4, count - 1);

            inst_ext.vertexAttribDivisorANGLE(id_loc, 0);

            for (let i = 0; i < attrib_names.length; i++) {
                inst_ext.vertexAttribDivisorANGLE(shader.attributes[attrib_names[i]], 0);
            }

        }

        this.draw_simple = function (mode, mvp, rot, params) {

            let shader;
            if (mode === "disc")
                shader = disc_shader;
            else if (mode === "arrow")
                shader = shaded_mesh_shader;
            else if (mode === "sphere")
                shader = plain_sphere_shader;
            else if (mode === "hemi_sphere")
                shader = hemi_sphere_shader;
            else if (mode === "shaded_sphere")
                shader = shaded_sphere_shader;
            else if (mode === "sun_eclipse")
                shader = sun_eclipse_shader;
            else if (mode === "parted_sphere")
                shader = parted_sphere_shader;
            else if (mode === "earth_simple")
                shader = earth_simple_shader;
            else if (mode === "earth_sdf")
                shader = earth_sdf_shader;
            else if (mode === "eclipse_light")
                shader = earth_sdf_eclipse_light_shader;
            else if (mode === "moon_eclipse_light")
                shader = moon_eclipse_light_shader;
            else if (mode === "earth")
                shader = earth_shader;
            else if (mode === "earth_sky")
                shader = earth_sky_shader;
            else if (mode === "moon_simple")
                shader = moon_simple_shader;
            else if (mode === "moon")
                shader = moon_shader;
            else if (mode === "sun")
                shader = sun_shader;
            else if (mode === "proto")
                shader = proto_shader;
            else if (mode === "tidal_water")
                shader = tidal_water_shader;
            else if (mode === "cone")
                shader = cone_shader;
            else if (mode === "shadow_cone")
                shader = shadow_cone_shader;

            gl.useProgram(shader.shader);

            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));
            gl.uniformMatrix3fv(shader.uniforms["u_rot"], false, mat3_invert(rot));

            if (mode === "disc") {

                gl.bindBuffer(gl.ARRAY_BUFFER, quad_vertex_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_pos"]);
                gl.vertexAttribPointer(shader.attributes["v_pos"], 2, gl.FLOAT, false, 2 * float_size, 0);

                gl.uniform4fv(shader.uniforms["u_color"], params.color);
                gl.uniform4fv(shader.uniforms["u_coords"], params.coords || [1, 1, 0, 0]);
                gl.uniform1f(shader.uniforms["u_feather"], params.feather);

                gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);

            } else if (mode === "cone" || mode === "shadow_cone") {

                gl.bindBuffer(gl.ARRAY_BUFFER, cone_vertex_buffer);
                gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, cone_index_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_pos"]);
                gl.vertexAttribPointer(shader.attributes["v_pos"], 3, gl.FLOAT, false, 3 * float_size, 0);

                gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));

                gl.uniform4fv(shader.uniforms["u_color"], params.color);

                if (mode === "shadow_cone") {
                    gl.uniform4fv(shader.uniforms["u_params"], params.params);
                    gl.uniform1f(shader.uniforms["u_norm_z"], params.norm_z);
                }

                gl.drawElements(gl.TRIANGLES, cone_index_count, gl.UNSIGNED_INT, 0);

            } else if (mode === "arrow") {
                gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, arrow_index_buffer);

                gl.bindBuffer(gl.ARRAY_BUFFER, arrow_vertex_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_pos"]);
                gl.vertexAttribPointer(shader.attributes["v_pos"], 3, gl.FLOAT, false, 7 * float_size, 0);

                gl.enableVertexAttribArray(shader.attributes["v_norm"]);
                gl.vertexAttribPointer(shader.attributes["v_norm"], 3, gl.FLOAT, false, 7 * float_size, 3 * float_size);

                gl.enableVertexAttribArray(shader.attributes["v_shade"]);
                gl.vertexAttribPointer(shader.attributes["v_shade"], 1, gl.FLOAT, false, 7 * float_size, 6 * float_size);

                gl.uniform4fv(shader.uniforms["u_color"], params.color);

                gl.drawElements(gl.TRIANGLES, arrow_index_count, gl.UNSIGNED_INT, 0);
            } else if (mode === "sphere" || mode === "shaded_sphere" || mode === "earth" || mode === "earth_simple"
                || mode === "earth_sdf" || mode === "proto" || mode === "eclipse_light" || mode === "tidal_water"
                || mode === "moon" || mode === "moon_simple" || mode == "hemi_sphere" || mode == "sun_eclipse"
                || mode === "sun" || mode === "earth_sky" || mode === "moon_eclipse_light") {
                gl.bindBuffer(gl.ARRAY_BUFFER, sphere_vertex_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_pos"]);
                gl.vertexAttribPointer(shader.attributes["v_pos"], 3, gl.FLOAT, false, 3 * float_size, 0);

                gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));
                gl.uniformMatrix3fv(shader.uniforms["u_rot"], false, mat3_invert(rot));


                if (mode === "sphere" || mode === "shaded_sphere" || mode == "hemi_sphere") {
                    gl.uniform4fv(shader.uniforms["u_color"], params.color || [1, 0, 0, 1]);
                } else if (mode === "sun_eclipse") {
                    gl.uniform4fv(shader.uniforms["u_dir0"], params.dir0);
                    gl.uniform4fv(shader.uniforms["u_dir1"], params.dir1);
                    gl.uniform4fv(shader.uniforms["u_dir2"], params.dir2);
                    gl.uniform1f(shader.uniforms["u_dim"], params.dim);
                } else if (mode === "proto") {
                    gl.uniform4fv(shader.uniforms["u_color"], params.color || [1, 0, 0, 1]);
                    gl.uniform4fv(shader.uniforms["u_params"], params.params || [1, 1, 1, 1]);
                } else if (mode === "tidal_water") {
                    gl.uniform4fv(shader.uniforms["u_color"], params.color || [1, 0, 0, 1]);
                    gl.uniform4fv(shader.uniforms["u_p0"], params.p0 || [0, 0, 0, 0]);
                    gl.uniform4fv(shader.uniforms["u_p1"], params.p1 || [0, 0, 0, 0]);
                    gl.uniform4fv(shader.uniforms["u_params"], params.params || [0, 0, 0, 0]);
                } else if (mode === "earth_sdf") {
                    gl.uniform1f(shader.uniforms["u_clear"], params.clear || 0)
                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["earth_sdf"]);
                    gl.uniform1i(shader.uniforms["u_tex_base"], 0);

                } else if (mode === "earth_simple") {

                    if (params.blur === undefined)
                        params.blur = 0;

                    gl.uniform2f(shader.uniforms["u_blur"], cos(params.blur), sin(params.blur));

                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["earth_color"]);
                    gl.uniform1i(shader.uniforms["u_tex_base"], 0);

                    gl.activeTexture(gl.TEXTURE1);
                    gl.bindTexture(gl.TEXTURE_2D, textures["earth_clouds"]);
                    gl.uniform1i(shader.uniforms["u_tex_clouds"], 1);

                } else if (mode === "earth") {

                    if (params.blur === undefined)
                        params.blur = 0;
                    gl.uniform3fv(shader.uniforms["u_light_dir"], params.light_dir);
                    gl.uniform2f(shader.uniforms["u_blur"], cos(params.blur), sin(params.blur));

                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["earth_color"]);
                    gl.uniform1i(shader.uniforms["u_tex_base"], 0);

                    gl.activeTexture(gl.TEXTURE1);
                    gl.bindTexture(gl.TEXTURE_2D, textures["earth_clouds"]);
                    gl.uniform1i(shader.uniforms["u_tex_clouds"], 1);

                } else if (mode === "moon_simple") {

                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["moon_color"]);
                    gl.uniform1i(shader.uniforms["u_tex_base"], 0);
                } else if (mode === "moon") {

                    gl.uniform3fv(shader.uniforms["u_light_dir"], params.light_dir);

                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["moon_color"]);
                    gl.uniform1i(shader.uniforms["u_tex_base"], 0);
                } else if (mode === "eclipse_light") {
                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["earth_sdf"]);
                    gl.uniform1i(shader.uniforms["u_tex_base"], 0);

                    gl.uniform3fv(shader.uniforms["u_sun"], params.sun);
                    gl.uniform3fv(shader.uniforms["u_moon"], params.moon);
                } else if (mode === "moon_eclipse_light") {
                    gl.uniform3fv(shader.uniforms["u_sun"], params.sun);
                    gl.uniform3fv(shader.uniforms["u_earth"], params.earth);
                    gl.uniform1f(shader.uniforms["u_progress"], params.progress);
                } else if (mode === "earth_sky") {

                    gl.activeTexture(gl.TEXTURE0);
                    gl.bindTexture(gl.TEXTURE_2D, textures["noise"]);
                    gl.uniform1i(shader.uniforms["u_tex_noise"], 0);

                    gl.activeTexture(gl.TEXTURE1);
                    gl.bindTexture(gl.TEXTURE_2D, transmittance_texture);
                    gl.uniform1i(shader.uniforms["u_transmittance_tex"], 1);

                    gl.uniform3fv(shader.uniforms["u_light_dir"], params.light_dir);
                    gl.uniform3fv(shader.uniforms["u_view_dir"], params.view_dir);
                    gl.uniform1f(shader.uniforms["u_h"], params.h);
                }


                gl.activeTexture(gl.TEXTURE3);
                gl.bindTexture(gl.TEXTURE_2D, textures["noise"]);

                gl.uniform1i(shader.uniforms["u_tex_noise"], 3);

                gl.drawArrays(gl.TRIANGLES, 0, sphere_vertex_count);
            } else if (mode === "parted_sphere") {
                gl.useProgram(shader.shader);

                gl.bindBuffer(gl.ARRAY_BUFFER, parted_sphere_vertex_buffer);
                gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, parted_sphere_index_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_pos"]);
                gl.vertexAttribPointer(shader.attributes["v_pos"], 3, gl.FLOAT, false, 3 * float_size, 0);

                gl.uniform4fv(shader.uniforms["u_color"], params.color || [1, 0, 0, 1]);
                gl.uniform3fv(shader.uniforms["u_spread"], params.spread || [0, 0, 0]);

                gl.drawElements(gl.TRIANGLES, parted_sphere_index_count,
                    gl.UNSIGNED_INT, 0);
            }

        }

        this.draw_ellipse = function (mvp, rot, color, a, e, r, span, dashed) {

            let shader = ellipse_shader;
            let b = a * Math.sqrt(1 - e * e);
            let c = e * a;

            if (span === undefined) {
                span = 2 * pi;
            }

            mvp = mat4_mul(mvp, translation_mat4([-c, 0, 0]));

            if (color[3] != 1) {
                gl.enable(gl.BLEND);
                gl.disable(gl.CULL_FACE);
                gl.depthMask(false);
            }

            gl.useProgram(shader.shader);

            gl.bindBuffer(gl.ARRAY_BUFFER, curve_vertex_buffer);
            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, curve_index_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_st"]);
            gl.vertexAttribPointer(shader.attributes["v_st"], 2, gl.FLOAT, false, 2 * float_size, 0);

            gl.uniformMatrix4fv(shader.uniforms["m_mvp"], false, mat4_transpose(mvp));
            gl.uniformMatrix3fv(shader.uniforms["m_rot"], false, mat3_invert(rot));

            gl.uniform4fv(shader.uniforms["params"], [a, b, r, span]);
            gl.uniform4fv(shader.uniforms["color"], color);
            gl.uniform1f(shader.uniforms["normal_f"], 0.0);
            gl.uniform1f(shader.uniforms["dashed"], dashed ? 1 : 0);

            gl.drawElements(gl.TRIANGLES, curve_index_count,
                gl.UNSIGNED_INT, 0);
        }

        this.draw_segment = function (mvp, rot, color, p0, p1, r) {

            let shader = segment_shader;

            if (color[3] != 1) {
                gl.enable(gl.BLEND);
                gl.disable(gl.CULL_FACE);
                gl.depthMask(false);
            }

            gl.useProgram(shader.shader);

            gl.bindBuffer(gl.ARRAY_BUFFER, segment_vertex_buffer);
            gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, segment_index_buffer);

            gl.enableVertexAttribArray(shader.attributes["v_st"]);
            gl.vertexAttribPointer(shader.attributes["v_st"], 2, gl.FLOAT, false, 2 * float_size, 0);

            gl.uniformMatrix4fv(shader.uniforms["m_mvp"], false, mat4_transpose(mvp));
            gl.uniformMatrix3fv(shader.uniforms["m_rot"], false, mat3_invert(rot));


            gl.uniform3fv(shader.uniforms["p0"], p0);
            gl.uniform3fv(shader.uniforms["p1"], p1);
            gl.uniform4fv(shader.uniforms["color"], color);
            gl.uniform1f(shader.uniforms["r"], r);
            gl.uniform1f(shader.uniforms["normal_f"], 0.0);

            gl.drawElements(gl.TRIANGLES, segment_index_count, gl.UNSIGNED_INT, 0);
        }

        this.draw_tetrahedra = function (mvp, rot, params) {

            let prism = params.prism;
            let shader = prism ? tetra_prism_shader : tetra_shader;

            gl.useProgram(shader.shader);

            if (prism) {


                gl.bindBuffer(gl.ARRAY_BUFFER, tetra_prism_weights_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_weight"]);
                gl.vertexAttribPointer(shader.attributes["v_weight"], 4, gl.FLOAT, false, 4 * float_size, 0);

            } else {

                gl.bindBuffer(gl.ARRAY_BUFFER, tetra_weights_buffer);

                gl.enableVertexAttribArray(shader.attributes["v_weight"]);
                gl.vertexAttribPointer(shader.attributes["v_weight"], 4, gl.FLOAT, false, 8 * float_size, 0);

                gl.enableVertexAttribArray(shader.attributes["v_n_weight"]);
                gl.vertexAttribPointer(shader.attributes["v_n_weight"], 4, gl.FLOAT, false, 8 * float_size, 4 * float_size);
            }


            gl.bindBuffer(gl.ARRAY_BUFFER, tetrahedron_instance_vertex_buffer);

            let attrib_names = ["v_pos0", "v_pos1", "v_pos2", "v_pos3"];

            for (let i = 0; i < 4; i++) {
                let loc = shader.attributes[attrib_names[i]];
                gl.enableVertexAttribArray(loc);
                gl.vertexAttribPointer(loc, 3, gl.FLOAT, false, 12 * float_size, i * 3 * float_size);
                inst_ext.vertexAttribDivisorANGLE(loc, 1);
            }


            gl.uniformMatrix4fv(shader.uniforms["u_mvp"], false, mat4_transpose(mvp));
            gl.uniformMatrix3fv(shader.uniforms["u_rot"], false, mat3_invert(rot));

            gl.uniform3fv(shader.uniforms["u_light_dir"], params.light_dir);

            let count = params.count ? params.count : tetra_inst_count;

            if (prism)
                inst_ext.drawArraysInstancedANGLE(gl.TRIANGLE_STRIP, 0, 10, count);
            else
                inst_ext.drawArraysInstancedANGLE(gl.TRIANGLES, 0, 12, count);

            for (let i = 0; i < 4; i++) {
                inst_ext.vertexAttribDivisorANGLE(shader.attributes[attrib_names[i]], 0);
            }

        }

    }

    function Drawer(container, mode, args) {
        let self = this;

        all_drawers.push(self);
        all_containers.push(container);
        container.drawer = this;

        let wrapper = document.createElement("div");
        wrapper.classList.add("canvas_container");
        wrapper.classList.add("non_selectable");

        let canvas = document.createElement("canvas");
        canvas.classList.add("non_selectable");
        canvas.style.position = "absolute";
        canvas.style.top = "0";
        canvas.style.left = "0";
        canvas.style.width = "100%";
        canvas.style.height = "100%";

        this.canvas = canvas;

        wrapper.appendChild(canvas);
        container.appendChild(wrapper);

        let scale_button;
        let reset_button;

        let play_button = document.createElement("div");
        play_button.classList.add("play_pause_button");
        play_button.classList.add("white");

        play_button.onclick = function () {
            self.set_paused(!self.paused);
        }


        if (mode.startsWith("moon") || mode.startsWith("sky")) {
            this.loading_div = document.createElement("div");
            this.loading_div.classList.add("loading_text");
            this.loading_div.textContent = "Loading...";
            container.appendChild(this.loading_div);
        }


        let state;
        let slider_args = [0, 0, 0];

        let arcball;
        let two_axis;

        let width, height;
        let aspect;

        let rot = args.rotation ? args.rotation : ident_mat3;

        let vp = ident_mat4;
        let proj;
        let ortho_proj;

        this.paused = true;
        this.requested_repaint = false;
        this.requested_tick = false;
        this.first_draw = true;

        this.slider_args = slider_args;


        let control_sign = 1;
        let drag_size_scale = 1;

        if (args.has_arcball) {
            arcball = new ArcBall(rot, function () {
                rot = arcball.matrix.slice();
                request_repaint();
            });
        } else if (args.two_axis) {

            two_axis = new TwoAxis();
            two_axis.set_angles([0, 0]);

            if (args.two_axis.angles)
                two_axis.set_angles(args.two_axis.angles);
            if (args.two_axis.horizontal_limits)
                two_axis.set_horizontal_limits(args.two_axis.horizontal_limits);
            if (args.two_axis.vertical_limits)
                two_axis.set_vertical_limits(args.two_axis.vertical_limits);
            if (args.two_axis.vertical_limits)
                two_axis.set_vertical_limits(args.two_axis.vertical_limits);
            if (args.two_axis.flip)
                control_sign = -1;
            if (args.two_axis.drag_size_scale)
                drag_size_scale = args.two_axis.drag_size_scale;

            rot = two_axis.matrix.slice();

            two_axis.set_callback(function () {
                rot = two_axis.matrix.slice();
                request_repaint();
            });

            this.two_axis = two_axis;
        }

        function event_canvas_coordinates(e) {
            let x = e.clientX;
            let y = e.clientY;

            let r = canvas.getBoundingClientRect();
            return [(x - r.left), (y - r.top)];
        }

        let draggables = [];
        let dragged_index = -1;
        let drag_enabled = true;
        let drag_delta;

        if (args.has_draggables) {

            function hit_test(p) {
                if (!drag_enabled)
                    return -1;

                p = vec_scale(p, 1 / width);

                for (let i = draggables.length - 1; i >= 0; i--) {
                    let s = draggables[i].size;
                    s = s * s;
                    if (vec_len_sq(vec_sub(draggables[i].pos, p)) < s)
                        return i;
                }

                return -1;
            }

            canvas.addEventListener("mousemove", e => {

                if (dragged_index >= 0)
                    return;

                if (hit_test(event_canvas_coordinates(e)) >= 0) {
                    canvas.style.cursor = "grab";
                } else {
                    canvas.style.cursor = "default";
                }

                return true;
            }, false);


            new TouchHandler(canvas,
                function (e) {
                    let p = event_canvas_coordinates(e);

                    dragged_index = hit_test(p);

                    if (dragged_index >= 0) {
                        let ss_point = vec_scale(draggables[dragged_index].pos, width);
                        drag_delta = vec_sub(p, ss_point);
                        canvas.style.cursor = "grabbing";
                        return true;
                    }

                    return false;
                },
                function (e) {

                    if (dragged_index < 0)
                        return;

                    let p = event_canvas_coordinates(e);

                    let draggable = draggables[dragged_index];

                    let size = 2 * draggable.size * width;

                    p = vec_sub(p, drag_delta);
                    p = vec_scale(p, 1 / width);

                    if (draggable.limiter) {
                        p = draggable.limiter(p);
                    }
                    else {
                        p[0] = clamp(p[0], size / width, 1 - size / width);
                        p[1] = clamp(p[1], size / width, height * 0.95 / width - size / width);

                    }

                    draggable.pos = p;

                    request_repaint();
                    return true;
                },
                function (e) {
                    if (dragged_index < 0)
                        return;

                    let p = event_canvas_coordinates(e);

                    dragged_index = -1;

                    if (hit_test(p) >= 0) {
                        canvas.style.cursor = "grab";
                    } else {
                        canvas.style.cursor = "default";
                    }
                });
        }


        let control = arcball || two_axis;
        if (control) {
            new TouchHandler(canvas,
                function (e) {
                    let c = event_canvas_coordinates(e);

                    if (control && dragged_index < 0) {
                        control.start((width - c[0]) * control_sign, c[1] * control_sign);
                        return true;
                    }

                    return false;
                },
                function (e) {
                    let c = event_canvas_coordinates(e);

                    if (control && dragged_index < 0) {
                        control.update((width - c[0]) * control_sign, c[1] * control_sign, e.timeStamp);
                        rot = control.matrix.slice();
                        request_repaint();
                    }
                    return true;
                },
                function (e) {
                    if (control) {
                        control.end(e.timeStamp);
                    }
                });
        }


        this.force_start = false;

        this.set_paused = function (p, force_start) {

            self.force_start = force_start;
            
            if (self.paused == p)
                return;

            self.paused = p;

            if (self.paused) {
                play_button.classList.remove("playing");
                if (args.has_motion_blur)
                    self.request_repaint();
            } else {
                play_button.classList.add("playing");
                if (!self.requested_tick) {
                    self.requested_tick = true;
                    window.requestAnimationFrame(tick);
                }
            }
        }

        let sliders;
        let slider_default_values;
        this.set_sliders = function (s, v) { sliders = s; slider_default_values = v; }

        this.reset = function () {
            state = undefined;
        }

        let t = 0;
        let prev_timestamp = undefined;

        function tick(timestamp) {

            self.requested_tick = false;

            let rect = canvas.getBoundingClientRect();

            let wh = window.innerHeight || document.documentElement.clientHeight;
            let ww = window.innerWidth || document.documentElement.clientWidth;

            if (prev_timestamp === undefined)
                prev_timestamp = timestamp;

            if (!(rect.top > wh || rect.bottom < 0 || rect.left > ww || rect.right < 0)) {

                const dt = Math.min((timestamp - prev_timestamp) / 1000, 1.0 / 20.0);
                t += dt;

                if (self.active || args.draggables || args.locations)
                    self.repaint(dt);
            }

            if (self.paused) {
                prev_timestamp = undefined;
            } else {
                prev_timestamp = timestamp;
                window.requestAnimationFrame(tick);
            }
        }

        if (args.animated) {
            wrapper.appendChild(play_button);
            animated_drawers.push(this);
        }

        if (args.has_planet_scale) {
            scale_button = document.createElement("div");
            scale_button.classList.add("planet_scale_button");
            scale_button.onclick = function () {
                toggle_planet_scale();
            }

            wrapper.appendChild(scale_button);

            planet_scale_drawers.push(this);
        }

        if (args.needs_eph) {
            eph_drawers.push(this);
        }

        if (args.has_units) {
            unit_drawers.push(this);
        }

        if (args.has_global_location) {
            global_location_drawers.push(this);

            if (mode.startsWith("hemi")) {

                let locate_button = document.createElement("div");
                locate_button.classList.add("locate_button");
                wrapper.appendChild(locate_button);

                locate_button.onclick = function () {
                    geolocate(self.companion);
                }
            }
        }

        if (mode.startsWith("sph")) {
            this.sph = true;
        }

        if (args.has_reset) {

            reset_button = document.createElement("div");
            reset_button.classList.add("restart_button");
            reset_button.classList.add("white");

            reset_button.onclick = function () {
                self.reset();
                // self.set_paused(!args.reset_starts);
            }

            wrapper.appendChild(reset_button);
        }

        this.active = true;

        this.set_active = function (x) {

            if (this.active == x)
                return;

            this.active = x;
            if (x) {
                container.classList.add("active_container");
                container.classList.remove("inactive_container");
            } else {
                container.classList.remove("active_container");
                container.classList.add("inactive_container");
            }
        }

        if (args.simulated) {
            this.set_paused(false);
        }


        if (args.companion) {
            args.companion.companion = this;
            this.companion = args.companion;
        }


        function request_repaint(force = false, mark_companion = true) {
            if (self.requested_repaint || (!self.paused && !self.first_draw && !force))
                return;

            self.requested_repaint = true;
            window.requestAnimationFrame(function () {
                self.repaint();
            });

            if (args.companion && mark_companion)
                args.companion.request_repaint();
        }

        this.request_repaint = request_repaint;

        this.set_visible = function (x) {
            this.visible = x;
            if (x)
                request_repaint();
        }

        this.set_slider_arg = function (i, x, animated) {

            slider_args[i] = x;

            request_repaint();
        }


        this.set_draggable_pos = function (i, p) {
            if (draggables && i < draggables.length) {
                draggables[i].pos = p;
                draggables[i].changed = true;
                request_repaint();
            }
        }

        this.rot = function () {
            return rot;
        }

        this.set_rot = function (x) {
            rot = x;
            if (arcball)
                arcball.set_matrix(x);

            request_repaint();
        }


        this.set_angles = function (x, y) {

            if (two_axis)
                two_axis.set_angles([x, y]);

            rot = two_axis.matrix;
            request_repaint();
        }

        this.set_lat_lon = function (lat, lon) {
            if (!state)
                return;

            if (lat !== undefined)
                state.lat = lat;

            if (lon !== undefined)
                state.lon = lon;

            request_repaint();
        }



        this.reset();

        this.on_resize = function () {
            let new_width = wrapper.clientWidth;
            let new_height = wrapper.clientHeight;

            if (new_width == width && new_height == height)
                return;

            width = new_width;
            height = new_height;

            canvas.width = width * scale;
            canvas.height = height * scale;

            aspect = width / height;

            let proj_w = 13.50;
            let proj_h = proj_w / aspect;

            ortho_proj = [
                1 / proj_w, 0, 0, 0,
                0, 1 / proj_h, 0, 0,
                0, 0, -0.015, 0,
                0, 0, 0, 1
            ];

            let fov = pi * 0.18;
            let near = 1.0;
            let far = 30.0;

            let f = 1.0 / Math.tan(fov / 2);
            let rangeInv = 1 / (near - far);

            proj = [
                f / aspect, 0, 0, 0,
                0, f, 0, 0,
                0, 0, (near + far) * rangeInv, -1,
                0, 0, near * far * rangeInv * 2, 0
            ];


            proj = mat4_transpose(proj);
            proj = mat4_mul(proj, translation_mat4([0, 0, -6.5]));


            let pad = 5;
            let a_size = Math.max(width, height) - pad * 2;

            if (arcball)
                arcball.set_viewport(width / 2 - a_size / 2 + pad,
                    height / 2 - a_size / 2 + pad,
                    a_size, a_size);
            else if (two_axis)
                two_axis.set_size([width * drag_size_scale, height * drag_size_scale]);

            request_repaint();
        }


        this.repaint = function (dt = 0) {

            self.requested_repaint = false;

            if (!self.visible)
                return;

            if (width == 0 || height == 0)
                return;

            vp = mat4_mul(proj, mat3_to_mat4(rot));

            const ctx = canvas.getContext("2d");

            ctx.resetTransform();
            ctx.clearRect(0, 0, canvas.width, canvas.height);
            ctx.scale(scale, scale);
            ctx.setLineDash([]);

            let base_line_width = 1.5;

            let font_size = 20;

            if (window.innerWidth < 350)
                font_size = 14;
            else if (window.innerWidth < 400)
                font_size = 15;
            else if (window.innerWidth < 500)
                font_size = 18;

            ctx.lineCap = "round";
            ctx.lineJoin = "round";
            ctx.lineWidth = base_line_width;

            ctx.font = font_size + "px IBM Plex Sans";
            ctx.textAlign = "center";
            ctx.globalAlpha = 1.0;
            ctx.globalCompositeOperation = "source-over";


            if (mode.startsWith("moon")) {

                if (!eph && mode !== "moon5")
                    return;

                if (textures_ready && self.loading_div) {
                    self.loading_div.remove();
                    self.loading_div = undefined;
                }

                let t = new Date().getTime() / 86400000 + 2440587.5;
                t += slider_args[0] * 30;




                let moon_mat = rot;
                let dist = 50;

                let screen_pos = [0, 0, 2];
                let screen_up = [0, 0.97, 0];
                let screen_right = [0.97, 0, 0];
                let camera_pos = [0, 0, dist];

                moon_mat = mat3_transpose(moon_mat);

                screen_pos = mat3_mul_vec(moon_mat, screen_pos);
                camera_pos = mat3_mul_vec(moon_mat, camera_pos);

                screen_up = mat3_mul_vec(moon_mat, screen_up);
                screen_right = mat3_mul_vec(moon_mat, screen_right);


                let w = height;
                let h = height;

                if (mode === "moon7") {
                    w = width;

                    if (!state) {
                        state = {};
                        state.lat = 0.67416 * pi / 180;
                        state.lon = 23.47314 * pi / 180;
                    }

                    let lat = state.lat;
                    let lon = state.lon;


                    let screen_pos = [0, 0, 2];
                    let screen_up = [0, 0.97, 0];
                    let screen_right = [0.97, 0, 0];
                    let front = vec_norm(vec_cross(screen_up, screen_right));
                    let camera_pos = vec_sub(screen_pos, vec_scale(front, dist));


                    let near = 1e2;
                    let far = 1e6;

                    let f = 51;

                    let rangeInv = 1 / (near - far);

                    let proj = [
                        f, 0, 0, 0,
                        0, f, 0, 0,
                        0, 0, (near + far) * rangeInv, near * far * rangeInv * 2,
                        0, 0, -1, 0
                    ];

                    proj = mat4_mul(proj, translation_mat4(vec_neg(camera_pos)));
                    let mat = mat4_mul(proj, mat3_to_mat4(rot));


                    if (draggables.length == 0)
                        draggables = [{
                            pos: world_to_drag_sphere(lat, lon, 1, mat), size: 0.05, limiter: function (p) {

                                p = vec_scale(p, 2);
                                p = sphere_limiter(p);
                                p = vec_scale(p, 0.5);
                                return p
                            }
                        },
                        {
                            pos: world_to_drag_sphere(lat, lon, 1, mat), size: 0.05, limiter: function (p) {

                                p = vec_scale(p, 2);
                                p[0] -= 1;
                                p = sphere_limiter(p);
                                p = vec_scale(p, 0.5);
                                p[0] += 0.5;
                                return p
                            }
                        }
                        ];


                    if (dragged_index >= 0) {
                        let lat_lon;
                        if (dragged_index == 0) {
                            let p = vec_scale(draggables[0].pos, 2);
                            lat_lon = drag_to_world_sphere(p, 1, mat4_invert(mat));
                            draggables[1].pos = vec_add(draggables[0].pos, [0.5, 0]);
                        } else {
                            let p = vec_scale(draggables[1].pos, 2);
                            p[0] -= 1;
                            lat_lon = drag_to_world_sphere(p, 1, mat4_invert(mat));
                            draggables[0].pos = vec_add(draggables[1].pos, [-0.5, 0]);
                        }

                        lat = state.lat = lat_lon[0];
                        lon = state.lon = lat_lon[1];

                    } else {
                        draggables[0].pos = world_to_drag_sphere(lat, lon, 1, mat);
                        draggables[0].pos = vec_scale(draggables[0].pos, 0.5);

                        draggables[1].pos = vec_add(draggables[0].pos, [0.5, 0]);
                    }
                }


                gl.begin(w, h);


                {

                    if (mode === "moon5" || mode === "moon7") {

                        if (mode === "moon7")
                            gl.viewport(0, 0, h, h);

                        gl.draw_full("elevation_moon", {
                            // scale: zoom_sc,
                            camera_pos: camera_pos,
                            screen_pos: screen_pos,
                            screen_up: screen_up,
                            screen_right: screen_right,
                            mat: [1.17, 1.17, 0, 0],
                            height_scale: mode === "moon7" ? [1, 1] : [10.0, 0.1]
                        });
                    }

                    if (mode !== "moon5") {
                        let emb_pos = eph.emb_pos(t);
                        let moon_earth_pos = eph.moon_earth_pos(t);
                        let m_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, earth_moon_mass_ratio / (1 + earth_moon_mass_ratio)));
                        let moon_rot = eph.moon_rot_mat(t);
                        let light_dir = mat3_mul_vec(mat3_transpose(moon_rot), vec_norm(m_pos));
                        light_dir.push(1);

                        if (mode === "moon7")
                            gl.viewport(h, 0, h, h);

                        gl.draw_full("complex_moon", {
                            // scale: zoom_sc,
                            camera_pos: camera_pos,
                            screen_pos: screen_pos,
                            screen_up: screen_up,
                            screen_right: screen_right,
                            light_dir: light_dir,
                            mat: [1.15, 1.15, 0, 0],
                        });
                    }
                }


                ctx.drawImage(gl.finish(), 0, 0, w, h);


                if (mode === "moon1" || mode === "moon3") {
                    draw_date_and_time(width, 0, t, false, true);
                }

                if (mode === "moon5") {


                    ctx.translate(width * 0.8, height * 0.5);
                    let w = width * 0.03;
                    let h = height * 0.9;
                    let grd = ctx.createLinearGradient(0, h * 0.5, 0, -h * 0.5, 0);

                    let n = elevation_lut.length;

                    for (let i = 0; i < n; i++) {
                        let t = i / (n - 1);

                        let c = vec_scale(elevation_lut[i], 1 / 255);

                        grd.addColorStop(t, rgba_color_string(c));
                    }


                    ctx.fillStyle = grd;

                    ctx.lineWidth = 1.5;
                    ctx.globalCompositeOperation = "source-over";
                    ctx.roundRect(0, -h * 0.5, w, h, w * 0.1);
                    ctx.fill();

                    let min = -9178;
                    let max = 10786;

                    let zero = (0 - min) / (max - min);

                    ctx.save();
                    ctx.translate(0, h * 0.5 + -zero * h);

                    let step = 2000;
                    let suffix = " m";
                    let scale = 1;
                    let range = 4;

                    if (!metric) {
                        scale = 0.3048;
                        step = 5000 * 0.3048;
                        suffix = " ft"
                        range = 6;
                    }

                    ctx.fillStyle = "#ddd";


                    ctx.textAlign = "left";

                    ctx.font = round(font_size * 0.8) + "px IBM Plex Sans";


                    ctx.lineWidth = 1;

                    for (let i = -range; i <= range + 1; i++) {



                        let hh = i * step;
                        let t = -(hh) / (max - min);
                        let y = t * h;

                        let l = (t + 0.5) * 0.8 + 0.1;
                        ctx.strokeStyle = rgba_color_string([l, l, l, 0.4]);



                        ctx.strokeLine(0, y, w, y);

                        ctx.globalCompositeOperation = "source-over";

                        ctx.globalAlpha = 1;
                        let val = round(hh / scale);
                        let str = (val < 0 ? "−" : "") + comma_number(abs(val)) + suffix;
                        ctx.fillText(str, w * 1.5, y + font_size * 0.25);
                    }

                    ctx.restore();
                    ctx.lineWidth = 1;

                    ctx.strokeStyle = "#333";

                    ctx.roundRect(0, -h * 0.5, w, h, w * 0.1);

                    ctx.stroke();

                }


                if (draggables.length) {
                    ctx.fillStyle = "rgba(255, 255, 255, 0.7)";
                    ctx.strokeStyle = "#333";

                    function draw(x, y) {

                        let s = width * 0.02;
                        ctx.beginPath();
                        ctx.ellipse(x, y - s * 1.25, s * 0.3, s * 0.3, 0, 0, 2 * pi);

                        ctx.moveTo(x, y);
                        ctx.arcTo(x - s * 1.5, y - 2 * s, x, y - 2 * s, s * 0.75);
                        ctx.arcTo(x + s * 1.5, y - 2 * s, x, y, s * 0.75);
                        ctx.lineTo(x, y);

                        ctx.fill("evenodd");
                        ctx.stroke();

                    }

                    draw(width * draggables[0].pos[0], width * draggables[0].pos[1]);
                    draw(width * draggables[1].pos[0], width * draggables[1].pos[1]);
                }

            } else if (mode === "eclipse") {

                gl.begin(width, width);


                gl.draw_full("eclipse");



                ctx.drawImage(gl.finish(), 0, 0, width, width);
            } else if (mode.startsWith("brdf")) {

                let dist = 10.5;
                let screen_pos = [0, 0, 20];
                let screen_up = [0, 0.5, 0];
                let screen_right = [0.5, 0, 0];
                let front = vec_norm(vec_cross(screen_up, screen_right));
                let camera_pos = vec_sub(screen_pos, vec_scale(front, dist));

                let mvp;

                {
                    let near = 10.0;
                    let far = 260.0;

                    let f = dist * 2;

                    let rangeInv = 1 / (near - far);

                    let proj = [
                        f, 0, 0, 0,
                        0, f, 0, 0,
                        0, 0, (near + far) * rangeInv, near * far * rangeInv * 2,
                        0, 0, -1, 0
                    ];

                    proj = mat4_mul(proj, translation_mat4(vec_neg(camera_pos)));
                    mvp = mat4_mul(proj, mat3_to_mat4(rot));
                }



                let moon_mat = rot;
                moon_mat = mat3_invert(moon_mat);

                screen_pos = mat3_mul_vec(moon_mat, screen_pos);
                camera_pos = mat3_mul_vec(moon_mat, camera_pos);

                screen_up = mat3_mul_vec(moon_mat, screen_up);
                screen_right = mat3_mul_vec(moon_mat, screen_right);

                let aa = -(slider_args[0] - 0.5) * 3.5;
                let light_dir = [cos(aa), 0, sin(aa)];
                let view_dir = vec_neg(mat3_mul_vec(moon_mat, [0, 0, 1]));

                let intensity = 2.6;

                let w = width;
                let h = width;
                let size = width;
                let brdf = lambert_radiance;
                let marker = 1;

                if (mode === "brdf1") {
                    brdf = lambert_radiance;
                } else if (mode === "brdf2") {
                    brdf = hapke_radiance;
                } else if (mode === "brdf3") {
                    h = size = round(width * 0.5);
                    w = h * 2;
                    marker = 0;
                } else if (mode === "brdf4") {
                    brdf = hapke_radiance;
                } else if (mode === "brdf4a") {
                    brdf = hapke_radiance;
                    aa = -(self.companion.slider_args[0] - 0.5) * 3.5;
                    light_dir = [cos(aa), 0, sin(aa)];

                    let m = mat3_invert(self.companion.rot())

                    view_dir = vec_neg(mat3_mul_vec(m, [0, 0, 1]));
                }

                let norm = [1, 0, 0];

                let val = brdf(light_dir, view_dir, norm);
                val = intensity * val;
                val = linear_to_srgb(val);
                val = saturate(val);


                let stroke_scale = 0.342;
                let dash_length = 2 * pi * stroke_scale * size;

                let options = {
                    camera_pos: camera_pos,
                    screen_pos: screen_pos,
                    screen_up: screen_up,
                    screen_right: screen_right,
                    light_dir: light_dir,
                    marker: marker,
                };

                gl.begin(w, h);

                function draw_light_arrow(mvp, rot, aa, tx = 0, ty = 0) {

                    let arrow_scale = 0.02;
                    let arrow_dist = 1.2;


                    let params = {};
                    params.color = rgba_hex_color(color0h);

                    let mat = rot_x_mat4(pi);
                    mat = mat4_mul(scale_mat4(arrow_scale), mat);
                    mat = mat4_mul(translation_mat4([tx, ty, arrow_dist]), mat);
                    mat = mat4_mul(rot_y_mat4(pi / 2 - aa), mat);
                    mat = mat4_mul(mvp, mat);

                    let r = rot_x_mat3(pi);
                    r = mat3_mul(rot_y_mat3(pi / 2 - aa), r);
                    r = mat3_mul(rot, r);

                    gl.draw_simple("arrow", mat, r, params);

                }

                function draw_view_arrow(mvp, rot) {

                    let arrow_scale = 0.02;
                    let arrow_dist = 1.22;

                    let params = {};
                    params.color = rgba_hex_color(color2h);

                    let mat = rot_x_mat4(pi);
                    mat = mat4_mul(scale_mat4(arrow_scale), mat);
                    mat = mat4_mul(translation_mat4([0, 0, arrow_dist]), mat);
                    mat = mat4_mul(mvp, mat);

                    let r = rot_x_mat3(pi);
                    r = mat3_mul(rot, r);

                    gl.draw_simple("arrow", mat, r, params);

                }


                if (mode === "brdf3") {
                    gl.viewport(0, 0, size, size);

                }

                let an = 7;

                if (vec_dot(view_dir, light_dir) >= 0 && mode !== "brdf4a") {
                    gl.set_depth_test_enabled(true);
                    draw_light_arrow(mvp, rot, aa);
                    gl.set_blend_enabled(true);
                }
                gl.set_depth_test_enabled(false);

                if (mode === "brdf1") {
                    gl.draw_full("lambert_sphere", options);


                } else if (mode === "brdf2") {
                    gl.draw_full("hapke_sphere", options);
                } else if (mode === "brdf3") {
                    gl.draw_full("lambert_sphere", options);
                    gl.set_depth_test_enabled(true);

                    if (vec_dot(view_dir, light_dir) < 0)
                        draw_light_arrow(mvp, rot, aa);

                    gl.viewport(size, 0, size, size);

                    if (vec_dot(view_dir, light_dir) >= 0) {
                        draw_light_arrow(mvp, rot, aa);
                    }

                    gl.set_depth_test_enabled(false);
                    gl.draw_full("hapke_sphere", options);
                } else if (mode === "brdf4") {
                    gl.draw_full("hapke_sphere", options);
                    gl.set_depth_test_enabled(true);

                    let view_mat = mat4_mul(mvp, mat3_to_mat4(mat3_transpose(rot)));
                    view_mat = mat4_mul(translation_mat4([0, 0, -0.01]), view_mat);

                    draw_view_arrow(view_mat, ident_mat3);

                } else if (mode === "brdf4a") {
                    gl.set_depth_test_enabled(true);

                    let color_scale = [1, 1, 1, 1];
                    if (vec_dot(view_dir, norm) > 0) {
                        val = 0;
                        color_scale = [0.4, 0.4, 0.4, 1];
                    }

                    let mat = scale_mat4([1, 1, 0.3]);
                    mat = mat4_mul(rot_y_mat4(pi / 2), mat);
                    mat = mat4_mul(mvp, mat);
                    gl.draw_ellipse(mat, ident_mat3, vec_mul(rgba_hex_color(color3h), color_scale), 0.22, 0, 0.018);



                    mat = mat4_mul(mat, scale_mat4([1, 1, 0.1]));
                    gl.draw_ellipse(mat, ident_mat3, [val, val, val, 1], 0.11, 0, 0.11);

                    gl.draw_ellipse(mat4_mul(mat, translation_mat4([0, 0, -0.1])), ident_mat3, [0, 0, 0, 1], 0.11, 0, 0.11);


                    draw_light_arrow(mvp, rot, aa);

                    let m = mat3_invert(self.companion.rot())

                    let view_mat = mvp;
                    view_mat = mat4_mul(view_mat, mat3_to_mat4(m));

                    draw_view_arrow(view_mat, mat3_mul(rot, m));

                    {
                        let z = vec_norm(vec_cross(view_dir, light_dir));
                        let x = light_dir;
                        let y = vec_cross(x, z);

                        let mat = [
                            x[0], y[0], z[0],
                            x[1], y[1], z[1],
                            x[2], y[2], z[2]];

                        let mat0 = mat3_to_mat4(mat);
                        mat0 = mat4_mul(mvp, mat0);

                        let a = acos(vec_dot(light_dir, view_dir));
                        a = -pi + a;

                        gl.draw_ellipse(mat0, ident_mat3, rgba_hex_color(color1h, 0.3), 1.05, 0, 0.012, a);
                    }

                    gl.draw_segment(mvp, ident_mat3, rgba_hex_color(color2h, 0.3), [0, 0, 0], vec_scale(view_dir, -1.17), 0.009);
                    gl.draw_segment(mvp, ident_mat3, rgba_hex_color(color0h, 0.3), [0, 0, 0], vec_scale(light_dir, 1.15), 0.009);
                }

                gl.set_depth_test_enabled(true);


                if (mode !== "brdf4a") {

                    if (vec_dot(view_dir, light_dir) < 0) {
                        draw_light_arrow(mvp, rot, aa);
                    }

                    ctx.save();
                    ctx.strokeStyle = "rgba(255, 255, 255, 0.15)";
                    ctx.lineWidth = size * 0.003;
                    ctx.setLineDash([dash_length * 0.0015, dash_length * 0.0035]);

                    ctx.translate(size / 2, size / 2)
                    ctx.beginPath();
                    ctx.ellipse(0, 0, size * stroke_scale, size * stroke_scale, 0, 0, 2 * Math.PI);
                    ctx.stroke();
                    ctx.restore();

                }

                ctx.drawImage(gl.finish(), 0, 0, w, h);


                if (mode === "brdf1" || mode === "brdf2") {

                    if (vec_dot(view_dir, norm) > 0) {
                        val = 0;
                        ctx.globalAlpha = 0.3;
                    }

                    ctx.lineWidth = w * 0.009;

                    ctx.fillStyle = rgba_color_string([val, val, val, 1]);
                    ctx.strokeStyle = color3;

                    ctx.fillEllipse(w / 2, height * 0.94, w * 0.05);
                    ctx.strokeEllipse(w / 2, height * 0.94, w * 0.05);
                    ctx.globalAlpha = 1;
                } else if (mode === "brdf4a") {


                    let a = acos(vec_dot(light_dir, view_dir));
                    a = pi - a;
                    ctx.fillStyle = color1;

                    ctx.fillText("phase angle = " + pretty_angle(a), width / 2, height - font_size);


                } else if (mode === "brdf3") {

                    let data = [
                        0.266655, 0.522631,
                        0.26645, 0.443564,
                        0.265844, 0.393976,
                        0.264846, 0.359082,
                        0.263471, 0.332501,
                        0.26173, 0.311023,
                        0.259638, 0.292889,
                        0.257205, 0.277028,
                        0.254448, 0.2628,
                        0.251378, 0.249774,
                        0.248012, 0.237678,
                        0.244364, 0.22632,
                        0.240448, 0.215571,
                        0.236281, 0.205339,
                        0.231876, 0.195563,
                        0.227252, 0.186199,
                        0.222422, 0.177216,
                        0.217403, 0.168591,
                        0.212211, 0.160306,
                        0.206862, 0.152352,
                        0.201371, 0.144716,
                        0.195755, 0.13739,
                        0.190029, 0.130367,
                        0.184209, 0.123639,
                        0.178311, 0.117199,
                        0.17235, 0.111038,
                        0.16634, 0.105151,
                        0.160297, 0.0995273,
                        0.154236, 0.0941601,
                        0.14817, 0.0890406,
                        0.142112, 0.0841597,
                        0.136078, 0.0795093,
                        0.130079, 0.0750797,
                        0.124129, 0.0708625,
                        0.118239, 0.0668484,
                        0.112422, 0.0630288,
                        0.106687, 0.059395,
                        0.101047, 0.0559385,
                        0.0955107, 0.052651,
                        0.0900881, 0.0495244,
                        0.0847871, 0.0465502,
                        0.0796193, 0.0443544,
                        0.0745892, 0.042195,
                        0.069705, 0.0400749,
                        0.0649732, 0.037996,
                        0.0603997, 0.0359601,
                        0.0559899, 0.0339689,
                        0.0517482, 0.032024,
                        0.0476785, 0.0301269,
                        0.0437842, 0.0282793,
                        0.0400679, 0.0264822,
                        0.0365319, 0.0247377,
                        0.0331769, 0.0230462,
                        0.0300042, 0.0214094,
                        0.0270135, 0.0198283,
                        0.0242043, 0.0183038,
                        0.0215754, 0.0168371,
                        0.019125, 0.0154288,
                        0.0168506, 0.0140801,
                        0.0147494, 0.0127915,
                        0.0128175, 0.0115636,
                        0.0110509, 0.010397,
                        0.00944492, 0.00929202,
                        0.00799447, 0.00824964,
                        0.00669366, 0.0072696,
                        0.00553629, 0.00635235,
                        0.00451568, 0.00549784,
                        0.00362526, 0.00470663,
                        0.00285681, 0.00397829,
                        0.0022028, 0.0033124,
                        0.00165501, 0.00270925,
                        0.00120493, 0.00216815,
                        0.00084382, 0.00168984,
                        0.000561751, 0.00127124,
                        0.000350461, 0.000914634,
                        0.00019888, 0.000613779,
                        9.87799e-05, 0.000376962,
                        3.91342e-05, 0.000198811,
                        1.0924e-05, 8.13356e-05,
                        8.29195e-07, 1.31424e-05,
                        0, 0,
                    ];
                    let labels = [
                        "matte paint",
                        "lunar soil",
                    ]
                    ctx.strokeStyle = "#171717";
                    ctx.strokeLine(width * 0.5, 0, width * 0.5, height);



                    let a = acos(-vec_dot(view_dir, light_dir));
                    let pad = width * 0.035;

                    let h = floor(height * 0.2);
                    let w = floor(size - 2 * pad);
                    ctx.translate(pad, height - 2 * font_size)

                    let h_max = data[1];


                    for (let side = 0; side < 2; side++) {

                        ctx.save();
                        ctx.translate(0, -font_size);
                        ctx.scale(1, -1);

                        ctx.lineWidth = 1;

                        ctx.strokeStyle = "#555";

                        ctx.strokeLine(0, 0, w, 0);
                        ctx.strokeLine(0, 0, 0, h * 1.1);

                        ctx.lineWidth = 2.5;
                        let n = data.length / 2;
                        ctx.beginPath();
                        ctx.strokeStyle = "#ddd";

                        for (let i = 0; i < n; i++) {
                            let x = w * i / (n - 1);
                            let y = h * data[2 * i + side] / h_max;

                            ctx.lineTo(x, y);
                        }
                        ctx.stroke();

                        ctx.lineTo(w, 0);
                        ctx.lineTo(0, 0);

                        ctx.closePath();

                        ctx.save();

                        ctx.clip();
                        ctx.globalCompositeOperation = "destination-over";
                        ctx.globalAlpha = 0.7;

                        let grd = ctx.createLinearGradient(0, 0, 0, h);
                        grd.addColorStop(0, "#000");
                        grd.addColorStop(1, "#fff");

                        ctx.fillStyle = grd;
                        ctx.fill();

                        ctx.restore();


                        let ii = (a / pi) * (n - 1);
                        let d0 = data[2 * floor(ii) + side];
                        let d1 = data[2 * ceil(ii) + side];
                        let hh = lerp(d0, d1, ii - floor(ii));

                        ctx.fillStyle = ctx.strokeStyle = color1;
                        ctx.fillEllipse(w * a / pi, 0, 3);
                        ctx.globalAlpha = 0.4;
                        ctx.strokeLine(w * a / pi, 0, w * a / pi, hh * h / h_max);
                        ctx.globalAlpha = 1;
                        ctx.fillEllipse(w * a / pi, hh * h / h_max, 2);

                        {
                            ctx.save();
                            ctx.fillStyle = ctx.strokeStyle = "#eee";
                            ctx.lineCap = "butt";
                            ctx.lineWidth = 1;
                            ctx.translate(0, h * 1.2);
                            ctx.fillEllipse(0, 0, h * 0.025);
                            let n = 10;
                            for (let i = 0; i < n; i++) {
                                ctx.strokeLine(0, h * 0.035, 0, h * 0.06);
                                ctx.rotate(2 * pi / n);
                            }

                            ctx.restore();
                        }

                        ctx.restore();


                        let f = ctx.font;
                        ctx.font = round(font_size * 0.75) + "px IBM Plex Sans";

                        ctx.fillStyle = "#666";
                        ctx.fillText("0°", 0, 0);
                        ctx.fillText("90°", 0.5 * (width * 0.5 - 2 * pad), 0);
                        ctx.fillText("180°", width * 0.5 - 2 * pad, 0);
                        ctx.font = f;

                        ctx.fillStyle = "#ddd";
                        ctx.fillText(labels[side], width * 0.25 - pad, font_size * 1.75);

                        ctx.translate(width / 2, 0);
                    }
                }



            } else if (mode === "shadow_hiding" || mode === "shadow_hiding2") {


                let mvp = vp;

                let fov = pi * 0.06;
                let near = 150.0;
                let far = 400.0;
                let dist = 350;

                let arrow_scale = 0.6;
                let arrow_dist = 20;

                let params = {};

                if (mode === "shadow_hiding") {
                    params.count = 28;
                    dist = 46;
                    near = 10;
                    arrow_scale = 0.1;
                    arrow_dist = 3.0;
                }

                let a = (slider_args[0] - 0.5) * Math.PI * 0.84;

                let dir = [sin(a), 0, cos(a)];

                params.light_dir = dir;

                let f = 1.0 / Math.tan(fov / 2);
                let rangeInv = 1 / (near - far);


                proj = [
                    f / aspect, 0, 0, 0,
                    0, f, 0, 0,
                    0, 0, (near + far) * rangeInv, -1,
                    0, 0, near * far * rangeInv * 2, 0
                ];


                proj = mat4_transpose(proj);
                proj = mat4_mul(proj, translation_mat4([0, 0, -dist]));


                mvp = mat4_mul(proj, mat3_to_mat4(rot));



                gl.begin(width, width);
                gl.set_depth_test_enabled(true);

                if (mode === "shadow_hiding") {

                    let mat = mat4_mul(mvp, scale_mat4(4));

                    let d = dir[2];
                    let shade = 0.01 + 0.99 * max(0.0, d);

                    let c = rgba_hex_color(0x555555);
                    c = vec_mul(c, c);

                    let params = {};
                    params.color = [sqrt(c[0] * shade), sqrt(c[1] * shade), sqrt(c[2] * shade), 1];
                    params.feather = 0.99;
                    gl.draw_simple("disc", mat, rot, params);
                }


                gl.draw_tetrahedra(mvp, rot, params);

                gl.set_shadow_geometry_stencil_pass();

                params.prism = true;
                gl.draw_tetrahedra(mvp, rot, params);

                gl.start_shadow_tint_pass();

                gl.draw_full("color_fill", { color: [0.07, 0.07, 0.07, 1.0] });
                gl.end_shadow_tint_pass();


                {
                    gl.set_stencil_test_enabled(false);
                    let params = {};
                    params.color = rgba_hex_color(0xF3C046);

                    let mat = rot_x_mat4(pi);
                    mat = mat4_mul(scale_mat4(arrow_scale), mat);
                    mat = mat4_mul(translation_mat4([0, 0, arrow_dist]), mat);
                    mat = mat4_mul(rot_y_mat4(a), mat);
                    mat = mat4_mul(mvp, mat);

                    let r = rot_x_mat3(pi);
                    r = mat3_mul(rot_y_mat3(a), r);
                    r = mat3_mul(rot, r);

                    gl.draw_simple("arrow", mat, r, params);
                }

                ctx.drawImage(gl.finish(), 0, 0, width, width);


            }

            else if (mode.startsWith("space_sim")) {


                const history_count = 1024;

                const sim_dt = 0.001;

                let zoom = 0.5;
                let camera_trail = false;

                let has_fixed = false;
                let has_local_trails = false;
                let has_barycenter = false;

                let v_arrow_scale = 3;

                let colors = [color0, color2, "#fff"];
                let grad_colors = [color0h, color2h, 0xffffff];


                if (mode === "space_sim5") {
                    has_fixed = true;
                } else if (mode === "space_sim6") {
                    has_fixed = true;
                    camera_trail = true;
                } else if (mode === "space_sim6a") {
                    has_fixed = true;
                    camera_trail = true;
                    has_barycenter = true;
                } else if (mode === "space_sim7" || mode === "space_sim7a") {
                    has_fixed = true;
                    camera_trail = true;
                    has_local_trails = true;
                    has_barycenter = true;
                } else if (mode === "space_sim8") {
                    has_fixed = true;
                    camera_trail = true;
                    has_local_trails = true;
                    has_barycenter = true;
                    colors = ["#999", "#4480BF", "#fff"];
                    grad_colors = [0x999999, 0x4480BF, 0xffffff];
                }

                function drag_to_world(p) {
                    return [(p[0] - 0.5 / (has_fixed ? aspect : 1)) / zoom, (p[1] - 0.5 / aspect) / zoom];
                }

                function world_to_drag(p) {
                    return [p[0] * zoom + 0.5 / (has_fixed ? aspect : 1), p[1] * zoom + 0.5 / aspect];
                }

                if (state === undefined) {
                    state = {};

                    if (mode === "space_sim1") {
                        state.masses = [1];
                        state.radii = [0.03];
                        state.pos = [[0.1, -0.2]];
                        state.vel = [[-0.1, 0.05]];
                        state.acc = [[0, 0]];
                    } else if (mode === "space_sim1a") {
                        state.masses = [1];
                        state.radii = [0.03];
                        state.pos = [[0.6, -0.4]];
                        state.vel = [[-0.1, 0.02]];
                        state.acc = [[0, 0]];
                    } else if (mode === "space_sim2") {
                        state.masses = [1, 3];
                        state.radii = [0.03, 0.043];
                        state.pos = [[0.3, -0.4], [0.5, 0.3]];
                        state.vel = [[-0.1, 0.05], [-0.09, -0.02]];
                        state.acc = [[0, 0], [0, 0]];
                    } else if (mode === "space_sim3") {
                        state.masses = [1, 20];
                        state.radii = [0.03, 0.08];
                        state.pos = [[0.6, -0.3], [0.6, 0.3]];
                        state.vel = [[-0.05, 0.00], [-0.15, 0.0]];
                        state.acc = [[0, 0], [0, 0]];
                    } else if (mode === "space_sim5" || mode === "space_sim6"
                        || mode === "space_sim6a" || mode === "space_sim7" || mode === "space_sim7a") {
                        state.masses = [1, 3];
                        state.radii = [0.03, 0.043];
                        state.pos = [[0.2, -0.2], [0.3, 0.1]];
                        state.vel = [[-0.15, 0.02], [-0.07, -0.01]];
                        state.acc = [[0, 0], [0, 0]];
                    } else if (mode === "space_sim8") {
                        state.masses = [0.01, 0.01 * earth_mass / moon_mass];
                        state.radii = [0.01, 0.01 * earth_radius / moon_radius];
                        state.pos = [[0.3, -0.2], [0.3, 0.1]];
                        state.vel = [[-0.1, 0.00], [-0.05, -0.0]];
                        state.acc = [[0, 0], [0, 0]];
                    } else if (mode === "space_sim10") {
                        state.masses = [0.01, 0.08, 0.64];
                        state.radii = [0.01, 0.02, 0.04];
                        state.pos = [[0.3, -0.2], [0.3, 0.1], [-0.1, 0.3]];
                        state.vel = [[-0.1, 0.00], [-0.05, -0.0], [-0.0, 0.06]];
                        state.acc = [[0, 0], [0, 0], [0, 0]];
                    }




                    play_button.hidden = false;
                    reset_button.hidden = true;

                    if (self.force_start)
                        self.force_start = false;
                    else
                        this.set_paused(true);

                    drag_enabled = true;

                    state.initial_pos = [state.pos[0]];

                    state.count = state.masses.length;
                    state.hist_count = state.count * (has_local_trails ? 2 : 1) + (camera_trail ? 1 : 0);
                    state.hist = new Float32Array(history_count * 3 * state.hist_count);
                    state.hist.fill(NaN);
                    state.hist_i = 0;

                    state.state = 0;
                    state.t = 0;


                    state.ddt = 0;


                    if (draggables.length) {

                        for (let i = 0; i < state.count; i++)
                            state.vel[i] = vec_scale(vec_sub(drag_to_world(draggables[2 * i + 1].pos), drag_to_world(draggables[2 * i + 0].pos)), 1 / v_arrow_scale);
                    }
                }


                if (draggables.length == 0) {



                    if (mode === "space_sim1" || mode === "space_sim1a") {
                        draggables = [
                            { pos: world_to_drag(state.pos[0]), size: 0.035 },
                            { pos: world_to_drag(state.pos[0]), size: 0.035 }]
                    } else if (mode === "space_sim2" || mode === "space_sim3") {

                        draggables = [
                            { pos: world_to_drag(state.pos[0]), size: 0.035 },
                            { pos: world_to_drag(state.pos[0]), size: 0.035 },
                            { pos: world_to_drag(state.pos[1]), size: 0.035 },
                            { pos: world_to_drag(state.pos[1]), size: 0.035 },
                        ]
                    } else if (mode === "space_sim5" || mode === "space_sim6" || mode === "space_sim6a"
                        || mode === "space_sim7" || mode === "space_sim7a" || mode === "space_sim8") {

                        function limiter(p) {
                            p[0] = clamp(p[0], 0.06, 0.44);
                            p[1] = clamp(p[1], 0.06, 0.44);
                            return p;
                        }
                        draggables = [
                            { pos: world_to_drag(state.pos[0]), size: 0.035, limiter: limiter },
                            { pos: world_to_drag(state.pos[0]), size: 0.035, limiter: limiter },
                            { pos: world_to_drag(state.pos[1]), size: 0.035, limiter: limiter },
                            { pos: world_to_drag(state.pos[1]), size: 0.035, limiter: limiter },
                        ]
                    } else if (mode === "space_sim10") {
                        draggables = [
                            { pos: world_to_drag(state.pos[0]), size: 0.035 },
                            { pos: world_to_drag(state.pos[0]), size: 0.035 },
                            { pos: world_to_drag(state.pos[1]), size: 0.035 },
                            { pos: world_to_drag(state.pos[1]), size: 0.035 },
                            { pos: world_to_drag(state.pos[2]), size: 0.035 },
                            { pos: world_to_drag(state.pos[2]), size: 0.035 },
                        ]
                    }
                }

                if (state.state == 0) {
                    if (self.paused) {
                        if (dragged_index >= 0) {
                            let i = (dragged_index & 14) >> 1;
                            if ((dragged_index & 1) == 0) {
                                state.pos[i] = drag_to_world(draggables[dragged_index].pos);
                                draggables[dragged_index + 1].pos = world_to_drag(vec_add(state.pos[i], vec_scale(state.vel[i], v_arrow_scale)));
                            } else {
                                state.vel[i] = vec_scale(vec_sub(drag_to_world(draggables[dragged_index].pos), state.pos[i]), 1 / v_arrow_scale);
                            }
                        } else {
                            for (let i = 0; i < state.count; i++) {
                                state.pos[i] = drag_to_world(draggables[2 * i + 0].pos);
                                if (draggables[2 * i + 1].changed) {

                                    state.vel[i] = vec_scale(vec_sub(drag_to_world(draggables[2 * i + 1].pos),
                                        drag_to_world(draggables[2 * i].pos)), 1 / v_arrow_scale);
                                    draggables[2 * i + 1].changed = false;
                                } else {
                                    draggables[2 * i + 1].pos = world_to_drag(vec_add(state.pos[i], vec_scale(state.vel[i], v_arrow_scale)));
                                }
                            }
                        }

                    } else {
                        play_button.hidden = true;
                        reset_button.hidden = false;
                        this.set_paused(false);

                        state.hist_i = 0;
                        state.hist.fill(NaN);

                        canvas.style.cursor = "default";
                        drag_enabled = false;

                        state.state = 1;
                    }
                }


                if (state.state == 0 && mode !== "space_sim1" && mode !== "space_sim1a") {

                    let pos = state.pos.slice();
                    let vel = state.vel.slice();

                    state.hist_i = 0;

                    for (let j = 0; j < history_count - 1; j++) {

                        for (let i = 0; i < 30; i++) {
                            sim(sim_dt);
                        }
                        let c = state.count;

                        let k = state.hist_i;
                        for (let i = 0; i < c; i++) {
                            state.hist[(i * history_count + history_count - k) * 3 + 0] = state.pos[i][0];
                            state.hist[(i * history_count + history_count - k) * 3 + 1] = state.pos[i][1];
                            state.hist[(i * history_count + history_count - k) * 3 + 2] = 0;
                        }

                        if (camera_trail) {
                            state.hist[(c * history_count + history_count - k) * 3 + 0] = lerp(state.pos[0][0], state.pos[1][0], slider_args[0]);
                            state.hist[(c * history_count + history_count - k) * 3 + 1] = lerp(state.pos[0][1], state.pos[1][1], slider_args[0]);
                            state.hist[(c * history_count + history_count - k) * 3 + 2] = 0;
                        }

                        state.hist_i++;
                    }

                    state.hist_i = 0;
                    state.pos = pos;
                    state.vel = vel;
                }

                function sim(dt) {
                    let c = state.count;

                    for (let i0 = 0; i0 < c; i0++) {

                        let m0 = state.masses[i0];
                        let r0 = state.radii[i0];
                        for (let i1 = i0 + 1; i1 < c; i1++) {
                            let p0 = state.pos[i0];
                            let p1 = state.pos[i1];
                            let m1 = state.masses[i1];
                            let r1 = state.radii[i1];

                            let d = vec_sub(p0, p1);
                            let r = vec_len(d);

                            if (r < r0 + r1) {

                                let w0 = m0 / (m0 + m1);
                                let w1 = m1 / (m0 + m1);

                                let v0 = state.vel[i0];
                                let v1 = state.vel[i1];

                                let d_norm = vec_scale(d, 1 / r);

                                let proj0 = vec_scale(d_norm, vec_dot(v0, d_norm));
                                let proj1 = vec_scale(d_norm, vec_dot(v1, d_norm));

                                v0 = vec_sub(v0, proj0);
                                v1 = vec_sub(v1, proj1);

                                let v = vec_add(vec_scale(proj0, w0), vec_scale(proj1, w1));

                                state.vel[i0] = vec_add(v0, v);
                                state.vel[i1] = vec_add(v1, v);

                                continue;
                            }

                            let f = 0.001 / (r * r * r);
                            state.acc[i0] = vec_add(state.acc[i0], vec_scale(d, -f * m1));
                            state.acc[i1] = vec_add(state.acc[i1], vec_scale(d, f * m0));
                        }
                    }

                    for (let i = 0; i < c; i++) {
                        state.vel[i] = vec_add(state.vel[i], vec_scale(state.acc[i], dt));
                        state.pos[i] = vec_add(state.pos[i], vec_scale(state.vel[i], dt));

                        state.acc[i][0] = state.acc[i][1] = 0;
                    }
                }

                if (state.state == 1) {


                    dt *= 4;
                    dt += state.ddt;
                    let iters = floor(dt / sim_dt);

                    state.ddt = dt - iters * sim_dt;

                    for (let i = 0; i < iters; i++) {
                        sim(sim_dt);
                    }

                    let c = state.count;

                    let k = state.hist_i;

                    for (let i = 0; i < c; i++) {
                        state.hist[(i * history_count + k) * 3 + 0] = state.pos[i][0];
                        state.hist[(i * history_count + k) * 3 + 1] = state.pos[i][1];
                        state.hist[(i * history_count + k) * 3 + 2] = 0;
                    }

                    if (camera_trail) {
                        state.hist[(c * history_count + k) * 3 + 0] = lerp(state.pos[0][0], state.pos[1][0], slider_args[0]);
                        state.hist[(c * history_count + k) * 3 + 1] = lerp(state.pos[0][1], state.pos[1][1], slider_args[0]);
                        state.hist[(c * history_count + k) * 3 + 2] = 0;
                    }
                }

                if (has_local_trails) {
                    let n = history_count - 1;
                    let camera_pos = vec_lerp(state.pos[0], state.pos[1], slider_args[0]);

                    for (let c = 0; c < state.count; c++) {

                        for (let k = 0; k < n; k++) {

                            let i00 = 0 * history_count + (state.hist_i - k + history_count) % history_count;
                            let i10 = 1 * history_count + (state.hist_i - k + history_count) % history_count;

                            let t = k / n;

                            let p00x = state.hist[i00 * 3];
                            let p00y = state.hist[i00 * 3 + 1];

                            let p10x = state.hist[i10 * 3];
                            let p10y = state.hist[i10 * 3 + 1];

                            let c0x = lerp(p00x, p10x, slider_args[0]);
                            let c0y = lerp(p00y, p10y, slider_args[0]);

                            let p0x = camera_pos[0] - c0x + (c == 0 ? p00x : p10x);
                            let p0y = camera_pos[1] - c0y + (c == 0 ? p00y : p10y);

                            state.hist[((c + 3) * history_count + k) * 3 + 0] = p0x;
                            state.hist[((c + 3) * history_count + k) * 3 + 1] = p0y;
                            state.hist[((c + 3) * history_count + k) * 3 + 2] = 0;
                        }
                    }
                }




                function draw(moving_camera) {

                    ctx.save();


                    ctx.translate((has_fixed ? height : width) * 0.5, height * 0.5);
                    ctx.scale(width * zoom, width * zoom)

                    let camera_offset = [0, 0];
                    let camera_pos = [0, 0];

                    if (state.count > 1)
                        camera_pos = vec_lerp(state.pos[0], state.pos[1], slider_args[0]);

                    if (moving_camera) {
                        camera_offset = camera_pos;
                    }

                    ctx.translate(-camera_offset[0], -camera_offset[1]);


                    ctx.lineWidth = 2 / width;
                    ctx.lineCap = "butt";

                    if (has_local_trails) {

                        let s = 0.4;
                        ctx.save();

                        ctx.translate(camera_pos[0], camera_pos[1]);

                        ctx.fillStyle = "rgba(255, 255, 255, 0.05)";
                        ctx.strokeStyle = "rgba(255, 255, 255, 0.1)";

                        ctx.beginPath();
                        ctx.rect(-s, -s, 2 * s, 2 * s);
                        ctx.fill();
                        ctx.stroke();


                        ctx.restore();
                    }

                    ctx.globalAlpha = 1;

                    ctx.lineWidth = 0.004;

                    if (state.state == 0 && !moving_camera) {

                        let off = 0.02;

                        for (let i = 0; i < state.count; i++) {

                            let col = rgba_hex_color(grad_colors[i]);
                            col = vec_mul(col, [0.8, 0.8, 0.8, 1.0]);
                            let col2 = vec_mul(col, [0.6, 0.6, 0.6, 0.8]);

                            ctx.strokeStyle = rgba_color_string(col);
                            ctx.fillStyle = rgba_color_string(col2);

                            let dir = vec_norm(state.vel[i]);

                            let len = vec_len(state.vel[i]) * v_arrow_scale - 2 * (state.radii[i] + off);

                            if (len > 0) {
                                ctx.arrow(state.pos[i][0] + dir[0] * (state.radii[i] + off),
                                    state.pos[i][1] + dir[1] * (state.radii[i] + off),
                                    state.pos[i][0] + state.vel[i][0] * v_arrow_scale - dir[0] * (state.radii[i] + off),
                                    state.pos[i][1] + state.vel[i][1] * v_arrow_scale - dir[1] * (state.radii[i] + off),
                                    min(0.015, len * 0.15),
                                    min(0.04, len * 0.4),
                                    min(0.05, len * 0.5)
                                );

                                ctx.fill();
                                ctx.stroke();
                            }

                            ctx.globalAlpha = 0.5;
                            let c = 2 * pi * state.radii[i];
                            ctx.setLineDash([c / 30, c / 30]);
                            ctx.strokeEllipse(state.pos[i][0] + state.vel[i][0] * v_arrow_scale,
                                state.pos[i][1] + state.vel[i][1] * v_arrow_scale, state.radii[i]);
                            ctx.setLineDash([]);
                            ctx.globalAlpha = 1;
                        }
                    }


                    if (mode === "space_sim1a") {
                        ctx.strokeStyle = "#777";
                        ctx.lineWidth = 0.004;

                        let ll = vec_len(state.pos[0]);

                        let n = 110;
                        for (let i = 0; i < n; i += 2) {

                            let dl = 0.01;
                            let t0 = (i * dl) / ll;
                            let t1 = min(1.0, (i + 1) * dl / ll);

                            if (t0 >= 1.0)
                                break;

                            ctx.strokeLine(state.pos[0][0] * t0, state.pos[0][1] * t0, state.pos[0][0] * t1, state.pos[0][1] * t1);
                        }

                        ctx.fillStyle = color3;
                        ctx.fillEllipse(0, 0, 0.01);
                    }

                    if (has_fixed) {

                        ctx.strokeStyle = "rgba(255, 255, 255, 0.2)";
                        ctx.strokeLine(state.pos[0][0], state.pos[0][1], state.pos[1][0], state.pos[1][1]);

                        ctx.strokeStyle = "rgba(255, 255, 255, 0.3)";
                        ctx.fillStyle = "white";
                        ctx.strokeLine(state.pos[0][0], state.pos[0][1], camera_pos[0], camera_pos[1]);
                        ctx.fillEllipse(camera_pos[0], camera_pos[1], 0.01);
                    }

                    if (has_barycenter) {
                        let bar = state.masses[1] / (state.masses[0] + state.masses[1]);
                        draw_barycenter(lerp(state.pos[0][0], state.pos[1][0], bar),
                            lerp(state.pos[0][1], state.pos[1][1], bar), 0.01)
                    }

                    ctx.restore();

                }

                {
                    gl.begin(width, height);

                    gl.update_trail_buffer(state.hist);

                    gl.set_blend_enabled(true);

                    if (has_fixed)
                        gl.scissors(0, 0, height, height);

                    let an = round(history_count / 5);
                    let alpha = state.state == 0 ? an : max(0, state.hist_i - history_count + an);

                    let mat = translation_mat4([has_fixed ? -0.5 : 0.0, 0, 0]);
                    mat = mat4_mul(scale_mat4([zoom * 2, -zoom * 2 * width / height, 1]), mat);

                    let count = state.hist_count - (has_local_trails ? state.count : 0);
                    for (let i = 0; i < count; i++) {

                        gl.draw_trail(mat, ident_mat3, history_count * 3 * i, history_count, {
                            color: rgba_hex_color(grad_colors[i], 0.5),
                            alpha_range: [0, alpha, history_count, history_count + 1],
                            params: [0.002, width / height],
                        });
                    }


                    for (let i = 0; i < state.count; i++) {
                        let m = scale_mat4(state.radii[i]);
                        m = mat4_mul(translation_mat4([state.pos[i][0], state.pos[i][1], 0]), m);
                        m = mat4_mul(mat, m);

                        let c = rgba_hex_color(grad_colors[i]);


                        gl.draw_simple("proto", m, ident_mat3, { color: c, params: [0.4, 1.1, 1.92 + i * 10, 1] });
                    }

                    if (has_fixed) {
                        mat = mat4_mul(mat, translation_mat4([1, 0, 0]));

                        gl.scissors(height, 0, height, height);

                        let camera_pos = [0, 0];

                        if (state.count > 1)
                            camera_pos = vec_lerp(state.pos[0], state.pos[1], slider_args[0]);

                        camera_pos.push(0);


                        for (let i = 0; i < state.hist_count; i++) {

                            gl.draw_trail(mat, ident_mat3, history_count * 3 * i, history_count, {
                                offset: vec_neg(camera_pos),
                                color: rgba_hex_color(grad_colors[i], has_local_trails ? 0.2 : 0.6),
                                alpha_range: [0, alpha, history_count, history_count + 1],
                                params: [0.002, width / height],
                            });
                        }

                        if (has_local_trails) {
                            for (let i = 0; i < state.count; i++) {

                                gl.draw_trail(mat, ident_mat3, history_count * 3 * (i + 3), history_count, {
                                    offset: vec_neg(camera_pos),
                                    color: rgba_hex_color(grad_colors[i], 0.6),
                                    alpha_range: [0, 0, history_count - alpha, history_count],
                                    params: [0.002, width / height],
                                });
                            }
                        }

                        for (let i = 0; i < state.count; i++) {
                            let m = scale_mat4(state.radii[i]);
                            m = mat4_mul(translation_mat4([state.pos[i][0] - camera_pos[0],
                            state.pos[i][1] - camera_pos[1], 0]), m);
                            m = mat4_mul(mat, m);

                            let c = rgba_hex_color(grad_colors[i]);

                            gl.draw_simple("proto", m, ident_mat3, { color: c, params: [0.4, 1.1, 1.2 + i * 9, 1] });
                        }

                    }


                }


                ctx.drawImage(gl.finish(), 0, 0, width, height);

                ctx.save();

                if (has_fixed) {
                    ctx.rect(0, 0, height, height);
                    ctx.clip();
                }


                draw(false);


                ctx.feather((has_fixed ? height : width) * scale, height * scale,
                    canvas.height * 0.1, canvas.height * 0.1,
                    canvas.height * 0.1, canvas.height * 0.1);

                ctx.restore();

                if (has_fixed) {

                    ctx.strokeStyle = "#555";

                    ctx.lineWidth = 1;
                    ctx.strokeLine(width / 2, height * 0.05, width / 2, height * 0.95);

                    ctx.save();

                    ctx.translate(height, 0);
                    ctx.rect(0, 0, height, height);
                    ctx.clip();

                    draw(true);


                    ctx.feather((has_fixed ? height : width) * scale, height * scale,
                        canvas.height * 0.1, canvas.height * 0.1,
                        canvas.height * 0.1, canvas.height * 0.1, height * scale, 0);

                    ctx.restore();



                    ctx.fillStyle = "rgba(255,255,255,0.2)";
                    ctx.fillText("space view", height * 0.5, height - font_size * 0.5);
                    ctx.fillText("camera view", height * 1.5, height - font_size * 0.5);
                }


                if (state.state == 1 && dt != 0) {
                    state.hist_i++;
                    if (state.hist_i == history_count) {
                        state.hist.copyWithin(0, 3);
                        state.hist_i--;
                    }
                    state.t += dt;
                }

            } else if (mode === "fov") {

                let r = lerp(0.02, 0.08, slider_args[0]);


                if (draggables.length == 0) {
                    draggables = [
                        { pos: [0.6, 0.1], size: 0.0, limiter: ((x) => x) }]
                }

                {
                    draggables[0].pos[1] = 0.1;
                    draggables[0].pos[0] = clamp(draggables[0].pos[0], 0.35, 0.99 - r);
                }

                draggables[0].size = r;

                let sc = width;

                let p = draggables[0].pos;
                let o = 0.02;
                let d = p[0] - o;

                let s = r / d;
                let c = sqrt(1 - s * s);

                let half_a = asin(r / d);

                ctx.save();


                ctx.translate(o * sc, 0.1 * sc);

                ctx.strokeStyle = "#333";
                ctx.lineWidth = width * 0.003;
                ctx.lineCap = "butt"

                ctx.beginPath();
                ctx.arc(0, 0, 0.1 * width, 2, -2, true);
                ctx.stroke();


                ctx.strokeStyle = color0;

                ctx.lineWidth = width * 0.004;
                ctx.beginPath();
                ctx.arc(0, 0, 0.1 * width, half_a, -half_a, true);
                ctx.stroke();


                ctx.globalAlpha = 0.15;
                ctx.fillStyle = color0;
                ctx.beginPath();
                ctx.lineTo(0, 0);
                ctx.rotate(-half_a);
                ctx.lineTo((d * c) * sc, 0);
                ctx.rotate(2 * half_a);
                ctx.lineTo((d * c) * sc, 0);
                ctx.fill();

                ctx.globalAlpha = 1;
                ctx.fillStyle = ctx.strokeStyle = color1;

                let rr = 0.24 * sc;
                let as = min(0.1 * half_a, 0.0045) * sc;

                ctx.beginPath();
                ctx.lineTo(rr, 0);
                ctx.lineTo(rr - as, -as * 2);
                ctx.lineTo(rr + as, -as * 2);
                ctx.fill();
                ctx.rotate(-2 * half_a);

                ctx.beginPath();
                ctx.lineTo(rr, 0);
                ctx.lineTo(rr - as, as * 2);
                ctx.lineTo(rr + as, as * 2);
                ctx.fill();

                ctx.rotate(half_a);

                ctx.lineWidth = width * 0.0025;
                ctx.beginPath();
                ctx.arc(0, 0, rr, half_a - 0.015, -half_a + 0.015, true);
                ctx.stroke();


                ctx.textAlign = "right";
                ctx.fillText(pretty_angle(2 * half_a), rr * 0.95, font_size * 0.35);

                ctx.restore();

                ctx.fillStyle = "#DF1E1E";
                ctx.fillEllipse(o * sc, 0.1 * sc, sc * 0.003);

                ctx.fillStyle = sphere_gradient(p[0] * sc, p[1] * sc, r * sc,
                    rgba_hex_color(color0h)
                );
                ctx.fillEllipse(p[0] * sc, p[1] * sc, r * sc);

                let feather_size = canvas.height * 0.1;

                ctx.feather(width * scale, height * scale, 0, 0, feather_size, feather_size);

            } else if (mode === "gravity" || mode === "gravity2" || mode === "com") {

                let m0 = lerp(1, 100, slider_args[0]);
                let m1 = lerp(1, 100, slider_args[1]);

                let r0 = 0.02 * Math.cbrt(m0);
                let r1 = 0.02 * Math.cbrt(m1);



                if (draggables.length == 0) {
                    draggables = [
                        { pos: [0.35, 0.2], size: 0.0, limiter: ((x) => x) },
                        { pos: [0.65, 0.2], size: 0.0, limiter: ((x) => x) }]
                }

                let pad_x = 0.13;
                let yy = 0.33;

                {
                    draggables[0].pos[1] = draggables[1].pos[1] = 0.17;


                    let x0 = draggables[0].pos[0];
                    let x1 = draggables[1].pos[0];


                    if (width < 500) {
                        pad_x = 0.2;
                        yy = 0.29;
                    } else if (width < 600) {
                        pad_x = 0.14;
                        yy = 0.31;
                    }


                    x0 = clamp(x0, pad_x, (1 - pad_x) - r1 - r0);
                    x1 = clamp(x1, pad_x + r0 + r1, 1 - pad_x);

                    if (mode === "gravity2") {
                        draggables[0].pos[1] = draggables[1].pos[1] = yy;
                        x0 = pad_x;
                    }

                    if (dragged_index == 0 || sliders[0].dragged) {
                        x1 = max(x1, x0 + r0 + r1);
                    } else if (dragged_index == 1 || sliders[1].dragged) {
                        x0 = min(x0, x1 - r0 - r1);
                    }
                    draggables[0].pos[0] = x0;
                    draggables[1].pos[0] = x1;
                }


                draggables[0].size = r0;
                draggables[1].size = r1;

                let p0 = draggables[0].pos.slice();
                let p1 = draggables[1].pos.slice();


                if (mode === "gravity2") {
                    p0[0] = pad_x;
                    draggables[0].pos[0] = -1;
                }


                let sc = width;

                let dd = p1[0] - p0[0];


                let base_font = ctx.font;
                let small_font = round(font_size * 0.65) + "px IBM Plex Sans";

                let str_r = "r";
                let str_x = "×";
                let str_m = "m";
                let str_eq = "=";

                let w_r = ctx.measureText(str_r).width;
                let w_x = ctx.measureText(str_x).width;
                let w_m = ctx.measureText(str_m).width;
                let w_eq = ctx.measureText(str_eq).width;

                function pretty_weight(kg) {
                    if (metric)
                        return kg.toFixed(1) + " kg";
                    else
                        return (kg / 0.45359237).toFixed(1) + " lb";
                }

                function pretty_distance(m) {
                    if (metric)
                        return m.toFixed(3) + " m";
                    else
                        return (m / 0.3048).toFixed(3) + " ft";
                }

                let pad = font_size * 0.3;
                let str0 = `m  = ${pretty_weight(m0)}`;
                let str1 = `m  = ${pretty_weight(m1)}`;
                let w0 = ctx.measureText(str0).width + pad;
                let w1 = ctx.measureText(str1).width + pad;


                let d0 = max(0.0, w0 / 2 - dd * sc + r1 * sc);
                let d1 = max(0.0, w1 / 2 - dd * sc + r0 * sc);

                let wd = max(0.0, (p0[0] * sc - d0 + w0 / 2) - (p1[0] * sc + d1 - w1 / 2));

                d0 += wd / 2;
                d1 += wd / 2;


                let c0 = color0;
                let c1 = color2;



                ctx.globalAlpha = 0.9;
                ctx.fillStyle = c0;
                ctx.fillText(str0, p0[0] * sc - d0, p0[1] * sc + r0 * sc + font_size * 1.5);
                ctx.font = small_font;
                ctx.fillText("1", p0[0] * sc - d0 - w0 / 2 + w_m + pad, p0[1] * sc + r0 * sc + font_size * 1.7);
                ctx.font = base_font;

                ctx.fillStyle = c1;
                ctx.fillText(str1, p1[0] * sc + d1, p1[1] * sc + r1 * sc + font_size * 1.5);
                ctx.font = small_font;
                ctx.fillText("2", p1[0] * sc + d1 - w1 / 2 + w_m + pad, p1[1] * sc + r1 * sc + font_size * 1.7);
                ctx.font = base_font;
                ctx.globalAlpha = 1;


                gl.begin(width, height);

                let params = [
                    [p0, r0, color0h, 0],
                    [p1, r1, color2h, 1],
                ]
                for (let param of params) {

                    let mat = translation_mat4([-0.5, mode === "gravity2" ? -0.25 : -0.2, 0]);
                    mat = mat4_mul(scale_mat4([2, -2 * width / height, 1]), mat);

                    let m = scale_mat4(param[1]);
                    m = mat4_mul(translation_mat4([param[0][0], param[0][1], 0]), m);
                    m = mat4_mul(mat, m);

                    let c = rgba_hex_color(param[2]);

                    gl.draw_simple("proto", m, ident_mat3, { color: c, params: [0.4, 2.1, 2 + param[3] * 4, 1] });


                }

                ctx.drawImage(gl.finish(), 0, 0, width, height);

                let rr = max(r0, r1);


                let f = G * m0 * m1 / (dd * dd);


                if (mode === "gravity2") {

                    ctx.globalCompositeOperation = "destination-over";
                    ctx.strokeStyle = "#333";
                    ctx.strokeLine(p0[0] * sc, p0[1] * sc, 2000, p0[1] * sc);
                    ctx.strokeLine(p0[0] * sc, p0[1] * sc, p0[0] * sc, -2000);
                    ctx.globalCompositeOperation = "source-over";
                    ctx.globalAlpha = 1;


                    ctx.lineWidth = 3;
                    ctx.strokeStyle = "#ddd"
                    let n = 100;
                    ctx.beginPath();
                    for (let i = 0; i < n; i++) {
                        let t = i / n;
                        t = t * t;
                        let x = r0 + t * (0.95 - r0);
                        let f = G * m1 * m0 / (x * x) * 3e4;
                        ctx.lineTo((p0[0] + x) * sc, (p1[1] - f) * sc);
                    }

                    ctx.stroke();
                    ctx.lineWidth = 1.5;

                    let x = (p1[0] - p0[0]);
                    let y = G * m1 * m0 / (x * x) * 3e4;

                    ctx.strokeStyle = "rgba(240, 240, 240, 0.5)"

                    ctx.strokeLine(p0[0] * sc, p0[1] * sc, p0[0] * sc, p0[1] * sc + 0.03 * sc);
                    ctx.strokeLine(p1[0] * sc, (p1[1] - y) * sc, p1[0] * sc, p1[1] * sc + 0.03 * sc);

                    ctx.lineCap = "butt";
                    ctx.lineWidth = 2;
                    ctx.strokeStyle = ctx.fillStyle = color1;

                    ctx.strokeLine(p0[0] * sc, p0[1] * sc + 0.02 * sc,
                        p1[0] * sc, p1[1] * sc + 0.02 * sc);

                } else {


                    ctx.strokeStyle = "rgba(240, 240, 240, 0.5)"
                    ctx.strokeLine(p0[0] * sc, p0[1] * sc, p0[0] * sc, p0[1] * sc - (rr + 0.03) * sc);
                    ctx.strokeLine(p1[0] * sc, p1[1] * sc, p1[0] * sc, p1[1] * sc - (rr + 0.03) * sc);
                }


                if (mode === "gravity" || mode === "gravity2") {

                    ctx.fillStyle = "#bbb";
                    ctx.strokeStyle = "#222";

                    ctx.save();

                    ctx.globalAlpha = 0.9;
                    ctx.scale(sc, sc);
                    ctx.lineWidth = 1.5 / sc;
                    ctx.translate(p0[0], p0[1]);

                    let len = f * 3e4;

                    ctx.arrow(0, 0, len, 0,
                        min(0.01, len * 0.1),
                        min(0.03, len * 0.3),
                        min(0.05, len * 0.5)
                    );

                    ctx.arrow(0, 0, len, 0,
                        min(0.01, len * 0.1),
                        min(0.03, len * 0.3),
                        min(0.05, len * 0.5)
                    );
                    ctx.fill();
                    ctx.stroke();


                    ctx.translate(dd, 0);

                    ctx.arrow(0, 0, -len, 0,
                        min(0.01, len * 0.1),
                        min(0.03, len * 0.3),
                        min(0.05, len * 0.5)
                    )

                    ctx.arrow(0, 0, -len, 0,
                        min(0.01, len * 0.1),
                        min(0.03, len * 0.3),
                        min(0.05, len * 0.5)
                    )

                    ctx.fill();
                    ctx.stroke();

                    ctx.restore();

                    ctx.feather(width * scale, height * scale,
                        canvas.height * 0.05, canvas.height * 0.05,
                        canvas.height * 0.05, canvas.height * 0.05);

                    if (mode === "gravity") {
                        let f_str = `F = ${(f * 1e10).toFixed(1)} × 10      N`;
                        let wf = ctx.measureText(f_str).width;


                        ctx.fillText(f_str, width * 0.5, height - 0.5 * font_size);

                        ctx.font = small_font;
                        ctx.fillText("−10", width * 0.5 + wf / 2 - font_size * 1.6, height - 1.1 * font_size);
                        ctx.font = base_font;

                        ctx.lineCap = "butt";
                        ctx.lineWidth = 2;
                        ctx.strokeStyle = ctx.fillStyle = color1;

                        ctx.strokeLine(p0[0] * sc, p0[1] * sc - (rr + 0.02) * sc,
                            p1[0] * sc, p1[1] * sc - (rr + 0.02) * sc);

                        ctx.fillText(`r = ${pretty_distance(dd)}`, lerp(p0[0], p1[0], 0.5) * sc, p1[1] * sc - (rr + 0.02) * sc + -0.5 * font_size);

                    }
                } else if (mode === "com") {

                    let com = dd * m1 / (m1 + m0);

                    let mid = ((p0[0] + com) * sc);

                    ctx.lineCap = "butt";
                    ctx.lineWidth = 2;



                    let cr0 = color0;
                    let cr1 = color2;


                    let r0_str = `r  = ${pretty_distance(com)}`;
                    let r1_str = `r  = ${pretty_distance(dd - com)}`;
 
                    let w0 = ctx.measureText(r0_str).width + font_size * 0.3;
                    let w1 = ctx.measureText(r1_str).width + font_size * 0.3;

                    let x0 = (p0[0] + com * 0.5) * sc;
                    let x1 = (p1[0] - (dd - com) * 0.5) * sc;

                    x0 = min(x0, mid - w0 / 2);
                    x1 = max(x1, mid + w1 / 2);

                    let y = p1[1] * sc - (rr + 0.02) * sc + -0.5 * font_size;

                    ctx.globalAlpha = 0.6;
                    ctx.fillStyle = cr0;
                    ctx.fillText(r0_str, x0, y);
                    ctx.fillStyle = cr1;
                    ctx.fillText(r1_str, x1, y);

                    ctx.font = small_font;
                    ctx.fillStyle = cr0;
                    ctx.fillText("1", x0 - w0 / 2 + font_size * 0.65, y + font_size * 0.2);
                    ctx.fillStyle = cr1;
                    ctx.fillText("2", x1 - w1 / 2 + font_size * 0.65, y + font_size * 0.2);
                    ctx.font = base_font;

                    ctx.strokeStyle = cr0;
                    ctx.strokeLine(p0[0] * sc, p0[1] * sc - (rr + 0.02) * sc,
                        mid, p1[1] * sc - (rr + 0.02) * sc);

                    ctx.strokeStyle = cr1;
                    ctx.strokeLine(mid, p0[1] * sc - (rr + 0.02) * sc,
                        p1[0] * sc, p1[1] * sc - (rr + 0.02) * sc);

                    ctx.globalAlpha = 1;
                    ctx.lineWidth = 1.5;
                    ctx.strokeStyle = "rgba(240, 240, 240, 0.5)"
                    ctx.strokeLine(mid, p1[1] * sc, mid, p1[1] * sc - (rr + 0.03) * sc);

                    ctx.fillStyle = "#ddd";

                    let space = font_size * 0.25;
                    let digit_space = font_size * 0.55;

                    let w = (w_r + w_m + w_x) * 2 + w_eq + 3 * digit_space + 3 * space;

                    ctx.textAlign = "left";

                    let base_c = "#aaa";

                    y = height - 0.5 * font_size;
                    let sub_y = y + 0.1 * font_size;
                    let x = width * 0.5 - w / 2;

                    ctx.globalAlpha = 0.6;
                    ctx.fillStyle = cr0;
                    ctx.fillText(str_r, x, y);
                    x += w_r;
                    ctx.font = small_font;
                    ctx.fillText("1", x, sub_y);
                    ctx.font = base_font;
                    x += digit_space;
                    ctx.globalAlpha = 1;

                    ctx.fillStyle = base_c;
                    ctx.fillText(str_x, x, y);
                    x += w_x;
                    x += space;
                    ctx.fillStyle = c0;
                    ctx.fillText(str_m, x, y);
                    x += w_m;
                    ctx.font = small_font;
                    ctx.fillText("1", x, sub_y);
                    ctx.font = base_font;
                    x += digit_space

                    ctx.fillStyle = base_c;
                    ctx.fillText(str_eq, x, y);
                    x += w_eq;
                    x += space;

                    ctx.globalAlpha = 0.6;
                    ctx.fillStyle = cr1;
                    ctx.fillText(str_r, x, y);
                    x += w_r;
                    ctx.font = small_font;
                    ctx.fillText("2", x, sub_y);
                    ctx.font = base_font;
                    x += digit_space;
                    ctx.globalAlpha = 1;

                    ctx.fillStyle = base_c;
                    ctx.fillText(str_x, x, y);
                    x += w_x;
                    x += space;
                    ctx.fillStyle = c1;
                    ctx.fillText(str_m, x, y);
                    x += w_m;
                    ctx.font = small_font;
                    ctx.fillText("2", x, sub_y);

                    draw_barycenter((p0[0] + com) * sc, p0[1] * sc, 5);


                }

            } else if (mode === "earth_scale" || mode === "sun_scale") {

                let t = slider_args[0];

                let zoom_t = smooth_step(0, 0.9, t);
                let text_a = smooth_step(0.8, 1, t);

                let min_md = 356421.444843;
                let mean_md = 384996.758579;
                let max_md = 406706.971797;

                let min_sd = 147092592.395439;
                let mean_sd = 149618861.790100;
                let max_sd = 152100604.065147;



                let s0 = 0.8;
                let s1 = 0.12;

                if (mode === "sun_scale") {
                    s0 = 0.105;
                    s1 = 0.00027;
                }

                let sc = Math.exp(lerp(Math.log(s0), Math.log(s1), zoom_t));
                let earth_r = height * 0.5;
                let moon_r = earth_r * moon_radius / earth_radius;
                let sun_r = earth_r * sun_radius / earth_radius;

                let d_scale = sc * earth_r / earth_radius;

                let y = height - smooth_lerp(earth_r, height * 0.2, zoom_t * zoom_t);
                let x = smooth_lerp(width * 0.5, earth_r * sc, zoom_t * zoom_t);

                if (mode === "sun_scale") {
                    x = -mean_md * d_scale;
                    x += width * 0.98;
                }

                gl.begin(width, height);

                gl.set_depth_test_enabled(true);

                let ortho_proj = [
                    height / width, 0, 0, 0,
                    0, 1, 0, 0,
                    0, 0, -0.015, 0,
                    0, 0, 0, 1
                ];

                let rot = rot_x_mat3(-pi / 2);
                let mvp = mat4_mul(ortho_proj, mat3_to_mat4(rot));

                {

                    let light_dir = mat3_mul_vec(mat3_invert(rot), [0, 0, 1]);

                    let earth_mat = scale_mat4(sc);
                    earth_mat = mat4_mul(rot_y_mat4(0.436), earth_mat);
                    earth_mat = mat4_mul(mvp, earth_mat);
                    earth_mat = mat4_mul(translation_mat4([x * 2 / width - 1, 1 - y * 2 / height, 0]), earth_mat);
                    gl.draw_simple("earth_simple", earth_mat, rot, { "light_dir": light_dir });
                }


                let moon_mat = scale_mat4(sc * moon_radius / earth_radius);
                moon_mat = mat4_mul(rot_z_mat4(pi / 2), moon_mat);
                moon_mat = mat4_mul(mvp, moon_mat);
                let moon_light_dir = mat3_mul_vec(mat3_invert(rot), [0, 0, 1]);

                {

                    let moon_mat1 = mat4_mul(translation_mat4([(x + mean_md * d_scale) * 2 / width - 1, 1 - y * 2 / height, 0]), moon_mat);
                    gl.draw_simple("moon_simple", moon_mat1, rot, { "light_dir": moon_light_dir });
                }

                if (mode === "earth_scale") {

                    let moon_mat2 = mat4_mul(translation_mat4([(x + max_md * d_scale) * 2 / width - 1, 1 - y * 2 / height, 0]), moon_mat);
                    gl.draw_simple("moon_simple", moon_mat2, rot, { "light_dir": moon_light_dir });

                    let moon_mat3 = mat4_mul(translation_mat4([(x + min_md * d_scale) * 2 / width - 1, 1 - y * 2 / height, 0]), moon_mat);
                    gl.draw_simple("moon_simple", moon_mat3, rot, { "light_dir": moon_light_dir });

                } else {
                    ctx.fillStyle = "#fff";
                    ctx.fillEllipse(x - mean_sd * d_scale, y, sun_r * sc, sun_r * sc);
                }


                ctx.drawImage(gl.finish(), 0, 0, width, height);



                ctx.fillStyle = "#999";

                if (mode !== "earth_scale") {
                    ctx.fillStyle = "#fff";
                    ctx.fillEllipse(x - mean_sd * d_scale, y, sun_r * sc, sun_r * sc);
                }

                ctx.strokeStyle = "rgba(255, 255, 255, 0.2)";
                ctx.lineCap = "butt";
                ctx.lineWidth = 1;

                let font_size = floor(width * 0.0284);


                ctx.font = font_size + "px IBM Plex Sans";
                let spacing = font_size * 2.3;


                let line_offset = font_size * 0.4;

                if (mode === "sun_scale") {
                    let spacing = font_size * 1.5;
                    ctx.strokeLine(x, y, x, y + spacing);
                    ctx.strokeLine(x + mean_md * d_scale, y, x + mean_md * d_scale, y + spacing);

                    ctx.strokeStyle = color3;
                    ctx.lineWidth = 2;
                    ctx.strokeLine(x, y + spacing - line_offset, x + mean_md * d_scale, y + spacing - line_offset);
                    ctx.strokeStyle = "rgba(255, 255, 255, 0.2)";

                    ctx.fillStyle = "red";
                    let com = mean_md * moon_mass / (earth_mass + moon_mass);
                    let r = 1500 * d_scale
                    draw_barycenter(x + com * d_scale, y, r);
                }

                if (text_a > 0) {
                    ctx.globalAlpha = text_a;
                    let yt = y - height * 0.15;



                    let min_d = min_md;
                    let mean_d = mean_md;
                    let max_d = max_md;

                    if (mode === "sun_scale") {

                        x -= mean_sd * d_scale;
                        min_d = min_sd;
                        mean_d = mean_sd;
                        max_d = max_sd;
                    }

                    ctx.lineWidth = 1;
                    ctx.strokeLine(x, y, x, yt - 2 * spacing);

                    ctx.strokeLine(x + min_d * d_scale, y, x + min_d * d_scale, yt);
                    ctx.strokeLine(x + mean_d * d_scale, y, x + mean_d * d_scale, yt - spacing);
                    ctx.strokeLine(x + max_d * d_scale, y, x + max_d * d_scale, yt - 2 * spacing);

                    ctx.strokeStyle = "#aaa";
                    ctx.lineWidth = 2;

                    let c0 = "#DDA8A8";
                    let c1 = "#C4B897";
                    let c2 = "#7AB8BA";

                    ctx.strokeStyle = c0;
                    ctx.strokeLine(x, yt + line_offset, x + min_d * d_scale, yt + line_offset);

                    ctx.strokeStyle = c1;
                    ctx.strokeLine(x, yt - spacing + line_offset, x + mean_d * d_scale, yt - spacing + line_offset);

                    ctx.strokeStyle = c2;
                    ctx.strokeLine(x, yt - 2 * spacing + line_offset, x + max_d * d_scale, yt - 2 * spacing + line_offset);

                    ctx.fillStyle = "#ccc";

                    ctx.textAlign = "right";
                    ctx.fillStyle = c0;
                    ctx.fillText("min distance = ", width / 2, yt);
                    ctx.fillStyle = c1;
                    ctx.fillText("mean distance = ", width / 2, yt - spacing);
                    ctx.fillStyle = c2;
                    ctx.fillText("max distance = ", width / 2, yt - 2 * spacing);
                    ctx.textAlign = "left";

                    ctx.fillStyle = c0;
                    ctx.fillText(pretty_distance(min_d), width / 2, yt);
                    ctx.fillStyle = c1;
                    ctx.fillText(pretty_distance(mean_d), width / 2, yt - spacing);
                    ctx.fillStyle = c2;
                    ctx.fillText(pretty_distance(max_d), width / 2, yt - 2 * spacing);

                }


                if (mode === "earth_scale")
                    ctx.feather(width * scale, height * scale,
                        0, canvas.height * 0.07, 0, 0);
                else
                    ctx.feather(width * scale, height * scale,
                        canvas.height * 0.07, 0, 0, 0);


            } else if (mode.startsWith("table_image")) {
                let sc;
                let off = 0;

                if (mode === "table_image0") {
                    sc = 0.97 / earth_radius;
                } else {

                    let zoom_t = slider_args[0];
                    if (zoom_t != 0) {
                        let a = 0.;
                    }
                    let r = Math.exp(lerp(Math.log(sun_radius), Math.log(earth_radius), zoom_t))

                    off = 1.0 - r / sun_radius;
                    sc = 0.98 / r;
                }



                let w = width;
                let h = height;

                gl.begin(w, h);
                gl.set_depth_test_enabled(true);

                let ortho_proj = [
                    1, 0, 0, 0,
                    0, 1, 0, 0,
                    0, 0, -0.015, 0,
                    0, 0, 0, 1
                ];

                let mvp = mat4_mul(ortho_proj, mat3_to_mat4(rot));

                gl.viewport(0, 0, height, height);

                let light_dir = mat3_mul_vec(mat3_invert(rot), [1, 0, 0]);

                let moon_mat = scale_mat4(moon_radius * sc);
                moon_mat = mat4_mul(rot_z_mat4(-pi / 2), moon_mat);
                moon_mat = mat4_mul(mvp, moon_mat);
                gl.draw_simple("moon_simple", moon_mat, rot, { light_dir });


                gl.viewport(height, 0, height, height);

                light_dir = mat3_mul_vec(mat3_invert(rot), [0, 0, 1]);

                let earth_mat = scale_mat4(earth_radius * sc);
                earth_mat = mat4_mul(mvp, earth_mat);
                gl.draw_simple("earth_simple", earth_mat, rot, { light_dir });

                gl.viewport(width - height, 0, height, height);
                ctx.drawImage(gl.finish(), 0, 0, w, h);


                if (mode === "table_image1") {
                    let div = document.getElementById("sun");

                    div.style.width = div.style.height = (sun_radius * sc * height).toFixed(3) + "px";
                    div.style.left = (height * (2.025)).toFixed(3) + "px";
                    div.style.top = (-sun_radius * sc * height * 0.5 + height * 0.5).toFixed(3) + "px";
                }
            }

            else if (mode.startsWith("hemi")) {

                if (!eph)
                    return;

                let gl = gl_mini;

                let lat = global_lat;
                let lon = global_lon;

                let color_frame = true;
                let picker = false;
                let global_drag = false;
                let draw_lat_lon = false;

                let sun = false;

                let t = new Date().getTime() / 86400000 + 2440587.5;

                if (mode === "hemi1") {
                    t = eph.eph_start_date + 1.7;

                } else if (mode === "hemi1a" || mode === "hemi1b") {

                    t = eph.eph_start_date + 1.665;

                    let arg = self.companion.slider_args[0];

                    t += arg * 0.45;
                } else if (mode === "hemi1c") {
                    t = eph.eph_start_date + 1.5;

                    let arg = self.companion.slider_args[0];

                    t += arg * 1;
                } else if (mode === "hemi10") {
                    picker = true;
                    global_drag = true;
                    draw_lat_lon = true;
                } else if (mode === "hemi12" || mode === "hemi14") {
                    picker = true;
                    global_drag = true;
                    draw_lat_lon = true;


                } else if (mode === "hemi16") {
                    picker = true;
                    global_drag = true;


                } else if (mode === "hemi8" || mode === "hemi2" || mode === "hemi20" || mode === "hemi23") {
                    picker = true;
                    global_drag = true;
                    sun = true;
                } else if (mode === "hemi28") {
                    picker = true;
                    global_drag = true;
                    sun = true;
                } else if (mode === "hemi30" || mode === "hemi33" || mode === "hemi36") {
                    picker = true;
                    global_drag = true;
                    sun = true;
                }

                let artifical_sats = mode === "hemi1" || mode === "hemi1a" || mode === "hemi1b" || mode === "hemi1c";


                if (self.companion && self.companion.state) {
                    t = self.companion.state.time;
                }

                if (artifical_sats) {

                    lat = 37.293244 * Math.PI / 180;
                    lon = -122.058491 * Math.PI / 180;

                } else if (self.companion && self.companion.state) {

                    if (self.companion.state.lat != undefined)
                        lat = self.companion.state.lat;

                    if (self.companion.state.lon != undefined)
                        lon = self.companion.state.lon;
                }


                let moon_earth_pos = eph.moon_earth_pos(t);

                let e_pos = vec_scale(moon_earth_pos, -1 / (1 + earth_moon_mass_ratio));
                let m_pos = vec_scale(moon_earth_pos, earth_moon_mass_ratio / (1 + earth_moon_mass_ratio));

                let emb_pos = eph.emb_pos(t);


                let w = width;
                let h = width;

                const hemi_radius = 6000;

                let dist = 10;
                let screen_pos = [0, 0, picker ? 90000 : 160000];
                if (mode === "hemi1")
                    screen_pos[2] = 133000;

                let screen_up = [0, 1, 0];
                let screen_right = [1, 0, 0];

                let screen_off = vec_scale(e_pos, -1);

                let near = 1e2;
                let far = 1e7;

                let front = vec_cross(screen_up, screen_right);
                let camera_offset = vec_sub(screen_pos, vec_scale(front, dist));

                let r = rot;

                let f = dist;

                let rangeInv = 1 / (near - far);

                let proj = [
                    f, 0, 0, 0,
                    0, f, 0, 0,
                    0, 0, (near + far) * rangeInv, near * far * rangeInv * 2,
                    0, 0, -1, 0
                ];

                proj = mat4_mul(proj, translation_mat4(vec_neg(camera_offset)));


                let earth_rot = eph.earth_rot_mat(t);

                let local_observer_pos = [earth_radius * cos(lat) * cos(lon), earth_radius * cos(lat) * sin(lon), earth_radius * sin(lat)]

                let north = [0, 0, 1];

                let z = vec_norm(local_observer_pos);
                let x = vec_norm(vec_cross(north, z));
                let y = vec_cross(z, x);


                let local_mat = [
                    x[0], x[1], x[2],
                    y[0], y[1], y[2],
                    z[0], z[1], z[2]];


                let clear_earth = false;

                let mvp = mat4_mul(proj, mat3_to_mat4(r));
                if (mode === "hemi1b") {
                    let mm = mat3_transpose(earth_rot);
                    r = mat3_mul(r, mm);
                    mvp = mat4_mul(mvp, mat3_to_mat4(mm));
                    mvp = mat4_mul(mvp, translation_mat4(screen_off));
                } else if (mode === "hemi1a" || mode === "hemi1c" || global_drag) {
                    mvp = mat4_mul(mvp, translation_mat4(screen_off));

                } else {
                    mvp = mat4_mul(mvp, translation_mat4(screen_off));
                    mvp = mat4_mul(mvp, translation_mat4(vec_scale(mat3_mul_vec(earth_rot, local_observer_pos), -1)));
                }

                if (mode === "hemi1c") {
                    clear_earth = true;
                }



                let earth_mat = mat3_to_mat4(earth_rot);
                earth_mat = mat4_mul(translation_mat4(e_pos), earth_mat);
                earth_mat = mat4_mul(mvp, earth_mat);

                let moon_rot = eph.moon_rot_mat(t);
                let moon_mat = mat3_to_mat4(moon_rot);
                moon_mat = mat4_mul(translation_mat4(m_pos), moon_mat);
                moon_mat = mat4_mul(mvp, moon_mat);

                let observer_pos = vec_add(e_pos, mat3_mul_vec(earth_rot, local_observer_pos));






                if (global_drag) {


                    if (draggables.length == 0)
                        draggables = [{
                            pos: world_to_drag_sphere(lat, lon, earth_radius * 1.15, earth_mat), size: 0.1, limiter: sphere_limiter
                        }];


                    if (dragged_index >= 0) {

                        let lat_lon = drag_to_world_sphere(draggables[0].pos, earth_radius * 1.15, mat4_invert(earth_mat));

                        self.companion.state.lat = lat_lon[0];
                        self.companion.state.lon = lat_lon[1];
                        self.companion.request_repaint(false, false);
                    } else {
                        draggables[0].pos = world_to_drag_sphere(lat, lon, earth_radius * 1.15, earth_mat);
                    }
                }




                gl.begin(w, h);
                gl.set_depth_test_enabled(true);


                if (sun) {

                    let sun_earth_pos = vec_neg(vec_add(emb_pos, e_pos));
                    let inv_earth_rot = mat3_transpose(earth_rot);


                    let mat = scale_mat4(earth_radius);
                    let params = {};
                    let p = mode === "hemi30" || mode === "hemi33" ? moon_earth_pos : [0, 0, -1e20];

                    params.moon = mat3_mul_vec(inv_earth_rot, p);
                    params.sun = mat3_mul_vec(inv_earth_rot, sun_earth_pos);
                    gl.draw_simple("eclipse_light", mat4_mul(earth_mat, mat), ident_mat3, params);
                } else if (!clear_earth) {
                    let mat = scale_mat4(earth_radius);
                    gl.draw_simple("earth_sdf", mat4_mul(earth_mat, mat), ident_mat3, {});
                }


                if (self.companion && self.companion.view_angles) {

                    let angles = self.companion.view_angles;

                    let rot = rot_z_mat3(-angles[0]);

                    rot = mat3_mul(mat3_transpose(local_mat), rot);
                    rot = mat3_mul(earth_rot, rot);

                    let mat = translation_mat4([0, 0, 4]);

                    mat = mat4_mul(mat3_to_mat4(rot), mat);
                    mat = mat4_mul(scale_mat4(150), mat);
                    mat = mat4_mul(translation_mat4(vec_scale(observer_pos, 1.)), mat);
                    mat = mat4_mul(mvp, mat);


                    gl.set_depth_fail_enabled(true);
                    gl.set_blend_enabled(true);
                    gl.set_depth_write_enabled(false);
                    draw_figurine(gl, mat, mat3_mul(r, rot), -angles[1], -angles[1] + 1.3, false);
                    gl.set_depth_write_enabled(true);
                    gl.set_blend_enabled(true);
                    gl.set_depth_fail_enabled(false);

                    draw_figurine(gl, mat, mat3_mul(r, rot), -angles[1], -angles[1] + 1.3);



                }

                function draw_projection(size, pos, color) {

                    pos = vec_sub(pos, observer_pos);
                    let l = vec_len(pos);
                    let s = hemi_radius / l;

                    let z = vec_scale(pos, 1 / l);
                    let x = vec_norm(vec_cross([0, 0, 1], z));
                    let y = vec_cross(z, x);

                    let local_mat = [
                        x[0], y[0], z[0],
                        x[1], y[1], z[1],
                        x[2], y[2], z[2]];

                    pos = vec_add(observer_pos, vec_scale(pos, s));

                    let mat0 = scale_mat4([size * s, size * s, 1]);
                    mat0 = mat4_mul(mat3_to_mat4(local_mat), mat0);
                    mat0 = mat4_mul(translation_mat4(pos), mat0);
                    mat0 = mat4_mul(mvp, mat0);

                    gl.draw_simple("sphere", mat0, ident_mat3, { color: color });
                }



                let sat_pos0 = vec_add(e_pos, vec_scale(vec_norm([-1, -1, 0.7]), 13000.0));
                let sat_pos1 = vec_add(e_pos, vec_scale(vec_norm([-2, -2, 0.5]), 18000.0));
                let sat_pos2 = vec_add(e_pos, vec_scale(vec_norm([-1, -1.5, 0.5]), 18000.0));


                if (artifical_sats) {


                    {
                        let mat0 = scale_mat4(200);
                        mat0 = mat4_mul(translation_mat4(sat_pos0), mat0);
                        mat0 = mat4_mul(mvp, mat0);
                        gl.draw_simple("shaded_sphere", mat0, r, { color: rgba_hex_color(color0h) });

                        draw_projection(200, sat_pos0, rgba_hex_color(color0h))
                    }


                    {
                        let mat0 = scale_mat4(400);
                        mat0 = mat4_mul(translation_mat4(sat_pos1), mat0);
                        mat0 = mat4_mul(mvp, mat0);
                        gl.draw_simple("shaded_sphere", mat0, r, { color: rgba_hex_color(color4h) });

                        draw_projection(400, sat_pos1, rgba_hex_color(color4h))
                    }

                    {
                        let mat0 = scale_mat4(200);
                        mat0 = mat4_mul(translation_mat4(sat_pos2), mat0);
                        mat0 = mat4_mul(mvp, mat0);
                        gl.draw_simple("shaded_sphere", mat0, r, { color: rgba_hex_color(color2h) });

                        draw_projection(200, sat_pos2, rgba_hex_color(color2h))
                    }

                }


                if (color_frame && self.companion && !picker) {
                    let r = ident_mat3;
                    let rot = self.companion.rot();
                    let f = 2;
                    let fz = 1;

                    r = mat3_mul(local_mat, r);
                    r = mat3_mul(rot, r);
                    r = mat3_invert(r);


                    let proj = [
                        f, 0, 0, 0,
                        0, f, 0, 0,
                        0, 0, fz, 0,
                        0, 0, -1, 1,
                    ];

                    let inv = mat4_invert(proj);
                    inv = mat4_mul(mat3_to_mat4(r), inv);

                    let p00 = mat4_mul_vec4(inv, [-1, -1, -1, 0]);
                    p00 = vec_norm(p00.slice(0, 3));

                    let p01 = mat4_mul_vec4(inv, [-1, 1, -1, 0]);
                    p01 = vec_norm(p01.slice(0, 3));

                    let p10 = mat4_mul_vec4(inv, [1, -1, -1, 0]);
                    p10 = vec_norm(p10.slice(0, 3));

                    let p11 = mat4_mul_vec4(inv, [1, 1, -1, 0]);
                    p11 = vec_norm(p11.slice(0, 3));

                    const radius = hemi_radius;

                    function draw_arc(p0, p1, color) {
                        let cross = vec_cross(p0, p1);
                        let x = p1;
                        let z = vec_norm(cross);
                        let y = vec_cross(x, z);

                        let mat = [
                            x[0], y[0], z[0],
                            x[1], y[1], z[1],
                            x[2], y[2], z[2]];

                        let mat0 = mat3_to_mat4(mat);

                        mat0 = mat4_mul(translation_mat4(local_observer_pos), mat0);
                        mat0 = mat4_mul(earth_mat, mat0);

                        gl.draw_ellipse(mat0, r, color, radius, 0, 50, Math.asin(vec_len(cross)));
                    }

                    draw_arc(p00, p01, rgba_hex_color(color0h))
                    draw_arc(p10, p00, rgba_hex_color(color3h))
                    draw_arc(p10, p11, rgba_hex_color(color1h))
                    draw_arc(p11, p01, rgba_hex_color(color2h))
                }




                gl.set_blend_enabled(true);
                gl.set_depth_write_enabled(false);


                if (clear_earth) {
                    let mat = scale_mat4(earth_radius);
                    gl.draw_simple("earth_sdf", mat4_mul(earth_mat, mat), ident_mat3, { clear: 1 });
                }



                if (draw_lat_lon) {
                    let mat0 = mat4_mul(earth_mat, translation_mat4([0, 0, earth_radius * sin(lat)]));
                    gl.draw_ellipse(mat0, ident_mat3, rgba_hex_color(color2h, 0.5), earth_radius * cos(lat), 0, 50);

                    let mat1 = mat4_mul(earth_mat, mat4_mul(rot_z_mat4(lon), rot_x_mat4(pi / 2)));
                    gl.draw_ellipse(mat1, ident_mat3, rgba_hex_color(color0h, 0.5), earth_radius, 0, 50);

                }



                function draw_cone(target_r, target_pos, color) {

                    let dir = vec_sub(target_pos, observer_pos);
                    let l = vec_len(dir);
                    let c = target_r / l;
                    let s = sqrt(1 - c * c);
                    let r = target_r * s;
                    let h = l - c * r;

                    let z = vec_scale(dir, 1 / l);
                    let x = vec_norm(vec_cross([0, 0, 1], z));
                    let y = vec_cross(z, x);


                    let ra = [
                        x[0], x[1], x[2],
                        y[0], y[1], y[2],
                        z[0], z[1], z[2],
                    ];

                    ra = mat3_transpose(ra);

                    let mat0 = scale_mat4([r, r, h]);
                    mat0 = mat4_mul(mat3_to_mat4(ra), mat0);
                    mat0 = mat4_mul(translation_mat4(observer_pos), mat0);
                    mat0 = mat4_mul(mvp, mat0);

                    gl.draw_simple("cone", mat0, ident_mat3, { color: color });
                }


                if (artifical_sats) {
                    draw_cone(200, sat_pos0, rgba_hex_color(color0h, 0.2));
                    draw_cone(400, sat_pos1, rgba_hex_color(color4h, 0.2));
                    draw_cone(200, sat_pos2, rgba_hex_color(color2h, 0.2));

                }


                {
                    let color = vec_scale([1, 1, 1, 1], 0.25);

                    let e_ap0 = [0, 0, earth_radius * 1.05];
                    let e_ap1 = [0, 0, earth_radius * 1.2];

                    gl.draw_segment(earth_mat, rot, color, e_ap0, e_ap1, 50);

                    e_ap0 = [0, 0, -earth_radius * 1.05];
                    e_ap1 = [0, 0, -earth_radius * 1.2];

                    gl.draw_segment(earth_mat, rot, color, e_ap0, e_ap1, 50);
                }



                if (!picker) {

                    let hemi_mat = scale_mat4(hemi_radius);
                    hemi_mat = mat4_mul(mat3_to_mat4(mat3_transpose(local_mat)), hemi_mat);
                    hemi_mat = mat4_mul(translation_mat4(local_observer_pos), hemi_mat);
                    hemi_mat = mat4_mul(earth_mat, hemi_mat);

                    let t = clear_earth ? "sphere" : "hemi_sphere";
                    let a = clear_earth ? 0.1 : 0.15;
                    gl.draw_simple(t, hemi_mat, ident_mat3, { color: rgba_hex_color(0xffffff, a) });
                }

                let grad = ctx.createRadialGradient(w / 2, h / 2, 0, w / 2, h / 2, h / 2);

                for (let i = 0; i <= 32; i++) {
                    let t = i / 32;

                    let s = saturate(t);
                    s = 1.0 - s;
                    s = s * s;
                    s = saturate(3 * s);

                    grad.addColorStop(t, rgba_color_string([0, 0, 0, s]));
                }
                ctx.fillStyle = grad;
                ctx.fillRect(0, 0, w, h);

                ctx.drawImage(gl.finish(), 0, 0, w, h);


                if (mode === "hemi1a" || mode === "hemi1b" || mode === "hemi1c") {
                    ctx.feather(width * scale, height * scale,
                        canvas.height * 0.1, canvas.height * 0.1,
                        canvas.height * 0.1, canvas.height * 0.1);

                }
            }

            else if (mode.startsWith("sky")) {

                if (!eph)
                    return;

                if (textures_ready && self.loading_div) {
                    self.loading_div.remove();
                    self.loading_div = undefined;
                }

                let lat = 37.293244 * Math.PI / 180;
                let lon = -122.058491 * Math.PI / 180;

                let draw_sun = false;
                let history_count = 512;

                let moon_locked = false;
                let sun_locked = false;
                let eclipse = false;
                let artifical_sats = false;
                let draw_stars = true;
                let sat_locked = false;

                let has_land = false;
                let has_horizon = false;


                let t = new Date().getTime() / 86400000 + 2440587.5;

                let base_t = t;
                t += slider_args[0] * 1;

                let trail_t0 = t - 1.2;
                let trail_t1 = t + 1.2;
                let trail_alpha_range = 50;


                if (mode === "sky1" || mode === "sky2" || mode === "sky20" || mode === "sky23") {
                    draw_sun = true;
                    has_horizon = true;


                    if (mode === "sky2" || mode === "sky23") {
                        moon_locked = true;
                    }

                } else if (mode === "sky26") {
                    draw_sun = false;

                    t = 2460734.532;
                    t += slider_args[0] * 29.426;


                    moon_locked = true;
                    draw_stars = false;
                    lat = slider_args[2] ? -pi / 2 : pi / 2;
                    lon = 0;
                } else if (mode === "sky28") {

                    draw_sun = true;
                    sun_locked = true;
                    has_horizon = true;

                    let times = [
                        JD(2024, 11, 1 + (12 + 47 / 60) / 24),
                        JD(2024, 12, 1 + (6 + 21 / 60) / 24),
                        JD(2024, 12, 30 + (22 + 27 / 60) / 24),
                        JD(2025, 1, 29 + (12 + 36 / 60) / 24),
                        JD(2025, 2, 28 + (0 + 45 / 60) / 24),
                        JD(2025, 3, 29 + (10 + 58 / 60) / 24),
                        JD(2025, 4, 27 + (19 + 31 / 60) / 24),
                        JD(2025, 5, 27 + (3 + 2 / 60) / 24),
                        JD(2025, 6, 25 + (10 + 31 / 60) / 24),
                        JD(2025, 7, 24 + (19 + 11 / 60) / 24),
                        JD(2025, 8, 23 + (6 + 6 / 60) / 24),
                        JD(2025, 9, 21 + (19 + 54 / 60) / 24),
                        JD(2025, 10, 21 + (12 + 25 / 60) / 24),
                        JD(2025, 11, 20 + (6 + 47 / 60) / 24),
                        JD(2025, 12, 20 + (1 + 43 / 60) / 24),
                        JD(2026, 1, 18 + (19 + 52 / 60) / 24),
                        JD(2026, 2, 17 + (12 + 1 / 60) / 24),
                        JD(2026, 3, 19 + (1 + 23 / 60) / 24),
                        JD(2026, 4, 17 + (11 + 52 / 60) / 24),
                        JD(2026, 5, 16 + (20 + 1 / 60) / 24),
                        JD(2026, 6, 15 + (2 + 54 / 60) / 24),
                        JD(2026, 7, 14 + (9 + 43 / 60) / 24),
                        JD(2026, 8, 12 + (17 + 37 / 60) / 24),
                        JD(2026, 9, 11 + (3 + 27 / 60) / 24),
                        JD(2026, 10, 10 + (15 + 50 / 60) / 24),
                        JD(2026, 11, 9 + (7 + 2 / 60) / 24),
                        JD(2026, 12, 9 + (0 + 52 / 60) / 24),
                    ]

                    t = times[round((times.length - 1) * slider_args[0])];

                    trail_t0 = t - 1.1;
                    trail_t1 = t + 0.1;

                } else if (mode === "sky30" || mode === "sky33") {

                    sun_locked = true;
                    draw_sun = true;
                    eclipse = true;

                    has_horizon = true;

                    has_land = true;

                    t = 2460409.2;
                    t += slider_args[0] * 0.2;

                    if (mode === "sky33") {
                        t = 2460232.1;
                        t += slider_args[0] * 0.2;
                    }

                    trail_t0 = t - 1.1;
                    trail_t1 = t + 0.1;

                    if (!state) {
                        self.companion.request_repaint();
                    }

                } else if (mode === "sky36") {

                    draw_sun = true;

                    has_horizon = true;

                    has_land = true;

                    t = 2459891.823;
                    t += slider_args[0] * 0.27;

                    trail_t0 = t - 1.1;
                    trail_t1 = t + 0.1;

                    if (!state) {
                        self.companion.request_repaint();
                    }

                } else if (mode == "sky5" || mode == "sky6") {
                    artifical_sats = true;
                    has_land = true;
                    has_horizon = true;
                    draw_stars = false;
                    t = eph.eph_start_date + 1.9;
                    trail_t0 = t - 0.5;
                    trail_t1 = t + 0.5;


                } else if (mode === "sky6a" || mode === "sky6b") {
                    artifical_sats = true;
                    has_land = true;
                    has_horizon = true;
                    draw_stars = false;
                    t = eph.eph_start_date + 1.665;
                    t += slider_args[0] * 0.45;

                    trail_t0 = t - 0.5;
                    trail_t1 = t + 0.5;

                    if (mode === "sky6b") {
                        sat_locked = true;
                    }

                } else if (mode === "sky6c") {
                    artifical_sats = true;
                    has_horizon = true;
                    draw_stars = false;
                    t = eph.eph_start_date + 1.5;
                    t += slider_args[0];

                    trail_t0 = t - 0.5;
                    trail_t1 = t + 0.5;


                } else if (mode === "sky8") {

                    trail_t0 = base_t - 0.001;
                    trail_t1 = base_t + 1.001;

                    trail_alpha_range = 1;

                    has_horizon = true;

                } else if (mode === "sky10") {
                    moon_locked = true;

                } else if (mode === "sky11") {
                    t = new Date().getTime() / 86400000 + 2440587.5;
                    t += slider_args[0] * 30;
                    moon_locked = true;

                } else if (mode === "sky13") {
                    t = 2451536.5 + 9104.498;
                    moon_locked = true;
                } else if (mode === "sky13a") {
                    t = 2451536.5 + 9104.498 + 16.057;
                    moon_locked = true;
                } else if (mode === "sky14") {
                    t = 2460654.7;
                    t += slider_args[0] * 18.6 * 365;
                    history_count = trail_history_count;

                    trail_t0 = t - 15;
                    trail_t1 = t + 15;
                }

                if (!state) {
                    state = {};
                    state.hist = new Float32Array(history_count * 3 * 3);
                    this.state = state;
                }

                if (mode === "sky1" || mode === "sky2" || mode === "sky20" || mode === "sky23") {

                    if (!state.start_time) {
                        const now = global_start_date;
                        const midnight = new Date(now.getFullYear(), now.getMonth(), now.getDate());
                        state.start_time = midnight.getTime() / 86400000 + 2440587.5;

                        slider_args[1] = (now.getTime() - midnight.getTime()) / (24 * 3600 * 1000);
                        sliders[1].set_value(slider_args[1]);

                    }

                    t = state.start_time;
                    t += round(slider_args[0] * 30);

                    trail_t0 = t - 0.1;
                    trail_t1 = t + 1.1;

                    t += slider_args[1];



                }



                if (mode === "sky1" || mode === "sky2" || mode === "sky8" || mode === "sky10" || mode === "sky14" || mode === "sky20" || mode === "sky23" || mode === "sky28") {

                    lat = state.lat !== undefined ? state.lat : global_lat;
                    lon = state.lon !== undefined ? state.lon : global_lon;

                } else if (mode === "sky11") {

                    if (!state.lat)
                        state.lat = pi / 2;

                    if (!state.lon)
                        state.lon = 0;

                    lat = state.lat;
                    lon = state.lon;

                } else if (mode === "sky30") {
                    has_land = true;
                    if (!state.lat)
                        state.lat = 32.4748888 * Math.PI / 180;

                    if (!state.lon)
                        state.lon = -96.2764444 * Math.PI / 180;

                    lat = state.lat;
                    lon = state.lon;

                } else if (mode === "sky33") {
                    has_land = true;

                    if (!state.lat)
                        state.lat = 35.0844 * Math.PI / 180;

                    if (!state.lon)
                        state.lon = -106.6504 * Math.PI / 180;

                    lat = state.lat;
                    lon = state.lon;

                } else if (mode === "sky36") {
                    has_land = true;
                    moon_locked = true;

                    if (!state.lat)
                        state.lat = 37.293244 * Math.PI / 180;

                    if (!state.lon)
                        state.lon = -122.058491 * Math.PI / 180;

                    lat = state.lat;
                    lon = state.lon;

                } else if (mode === "sky40") {

                    t = 2460649.4;
                    moon_locked = true;
                    draw_sun = true;

                    lat = 1;
                    lon = 0.3;
                }

                state.time = t;


                let draw_outline = artifical_sats && (mode !== "sky5");


                let moon_earth_pos = eph.moon_earth_pos(t);
                let emb_pos = eph.emb_pos(t);

                let e_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, -1 / (1 + earth_moon_mass_ratio)));
                let m_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, earth_moon_mass_ratio / (1 + earth_moon_mass_ratio)));


                let local_observer_pos = [earth_radius * cos(lat) * cos(lon), earth_radius * cos(lat) * sin(lon), earth_radius * sin(lat)]

                let w = width;
                let h = height;

                if (mode === "sky13" || mode === "sky13a") {
                    h = height;
                    local_observer_pos = [0.01, 0.01, earth_radius];
                }

                let dist = (moon_locked || sun_locked) ? 150 : artifical_sats ? 2 : 4;

                if (mode === "sky14")
                    dist = 1.5;
                else if (mode === "sky28")
                    dist = 4;
                else if (mode === "sky36")
                    dist = 50;

                let screen_pos = [0, 0, 1];
                let screen_up = [0, 1, 0];
                let screen_right = [width / height, 0, 0];

                let near = artifical_sats ? 2e3 : 1e5;
                let far = 5e8;


                let front = vec_norm(vec_cross(screen_up, screen_right));
                let camera_offset = vec_sub(screen_pos, vec_scale(front, dist));


                let r = rot;

                let earth_rot = eph.earth_rot_mat(t);

                let observer_pos = vec_add(e_pos, mat3_mul_vec(earth_rot, local_observer_pos));




                let local_mat;


                {

                    let north = [0, 0, 1];

                    let z = vec_norm(local_observer_pos);
                    let x = vec_norm(vec_cross(north, z));
                    let y = vec_cross(z, x);

                    local_mat = [
                        x[0], y[0], z[0],
                        x[1], y[1], z[1],
                        x[2], y[2], z[2]];

                }

                let base_sat_pos0 = vec_scale(vec_norm([-1, -1, 0.7]), 13000.0);
                let base_sat_pos1 = vec_scale(vec_norm([-2, -2, 0.5]), 18000.0);
                let base_sat_pos2 = vec_scale(vec_norm([-1, -1.5, 0.5]), 18000.0);

                let sat_pos0 = vec_add(e_pos, base_sat_pos0);
                let sat_pos1 = vec_add(e_pos, base_sat_pos1);
                let sat_pos2 = vec_add(e_pos, base_sat_pos2);

                if (!self.view_angles && self.companion)
                    self.companion.request_repaint();

                if (moon_locked || sat_locked || sun_locked || self.first_draw) {


                    let target = m_pos;

                    if (sun_locked) {
                        target = [0, 0, 0];
                    } else if (artifical_sats) {
                        target = sat_pos2;

                        if (mode === "sky6a") {
                            target = vec_add(e_pos, vec_scale(vec_norm([-1, -0.55, 0.6]), 18000.0));
                        }
                    }
                    let dir = vec_norm(vec_sub(observer_pos, target));

                    dir = mat3_mul_vec(mat3_transpose(earth_rot), dir);
                    dir = mat3_mul_vec(mat3_transpose(local_mat), dir);

                    {
                        self.view_angles = [pi + atan2(dir[0], dir[1]), -pi / 2 + asin(dir[2])];

                        if (two_axis)
                            two_axis.set_angles(self.view_angles);
                    }

                    let z = dir;
                    let x = vec_norm(vec_cross([0, 0, 1], z));
                    let y = vec_cross(z, x);

                    let ra = [
                        x[0], x[1], x[2],
                        y[0], y[1], y[2],
                        z[0], z[1], z[2],
                    ]

                    rot = ra;

                    r = ident_mat3;

                    r = mat3_mul(mat3_transpose(earth_rot), r);
                    r = mat3_mul(mat3_transpose(local_mat), r);
                    r = mat3_mul(rot, r);

                } else {

                    self.view_angles = two_axis.angles;

                    r = ident_mat3;

                    r = mat3_mul(mat3_transpose(earth_rot), r);
                    r = mat3_mul(mat3_transpose(local_mat), r);
                    r = mat3_mul(rot, r);
                }


                let f = dist;

                let rangeInv = 1 / (near - far);

                let aspect = height / width;

                if (mode === "sky13" || mode === "sky13a") {

                    aspect = 1;
                }

                let proj = [
                    f * aspect, 0, 0, 0,
                    0, f, 0, 0,
                    0, 0, (near + far) * rangeInv, near * far * rangeInv * 2,
                    0, 0, -1, 0
                ];


                proj = mat4_mul(proj, translation_mat4(vec_neg(camera_offset)));




                let mvp = translation_mat4(vec_scale(observer_pos, -1));
                mvp = mat4_mul(mat3_to_mat4(r), mvp);
                mvp = mat4_mul(proj, mvp);



                let earth_mat = mat3_to_mat4(earth_rot);
                earth_mat = mat4_mul(translation_mat4(e_pos), earth_mat);
                earth_mat = mat4_mul(mvp, earth_mat);

                let moon_rot = eph.moon_rot_mat(t);
                let moon_mat = mat3_to_mat4(moon_rot);
                moon_mat = mat4_mul(translation_mat4(m_pos), moon_mat);
                moon_mat = mat4_mul(mvp, moon_mat);



                let local_sun_dir;

                {
                    let m = mat3_transpose(mat3_mul(earth_rot, local_mat));
                    local_sun_dir = vec_norm(mat3_mul_vec(m, vec_neg(observer_pos)));

                }


                gl.create_transmittance_lut();

                gl.update_sky_lut_texture(local_sun_dir, 0);


                gl.begin(w, h);


                if (mode === "sky13") {
                    gl.viewport(0, 0, height, height);
                } else if (mode === "sky13a") {
                    gl.viewport(-width, 0, height, height);
                }

                gl.set_depth_write_enabled(false);

                if (draw_sun && !eclipse) {
                    let mat = rot;
                    mat = mat3_invert(mat);

                    let options = {
                        camera_pos: mat3_mul_vec(mat, camera_offset),
                        screen_pos: mat3_mul_vec(mat, screen_pos),
                        screen_up: mat3_mul_vec(mat, screen_up),
                        screen_right: mat3_mul_vec(mat, screen_right),
                        light_dir: local_sun_dir,
                    };
                    gl.draw_full("sky", options);

                }

                gl.set_blend_enabled(true);



                if (draw_stars) {
                    gl.set_depth_test_enabled(true);
                    gl.set_depth_write_enabled(true);
                    gl.set_color_write_enabled(false);

                    gl.draw_simple("sphere", mat4_mul(moon_mat, scale_mat4(moon_radius)), rot, { color: [1, 0, 0, 1] });

                    gl.set_color_write_enabled(true);
                    gl.set_depth_write_enabled(false);

                    let m = mat3_to_mat4(r);
                    m = mat4_mul(proj, m);
                    gl.set_blend_mode("dover");
                    gl.draw_stars(m);
                    gl.set_blend_mode("sover");
                }



                gl.set_depth_write_enabled(true);
                gl.set_depth_test_enabled(true);

                let followed_bodies = [];

                if (artifical_sats) {

                    followed_bodies = [sat_pos0, sat_pos1, sat_pos2];



                    {
                        let mat0 = scale_mat4(200);
                        mat0 = mat4_mul(translation_mat4(sat_pos0), mat0);
                        mat0 = mat4_mul(mvp, mat0);
                        gl.draw_simple("shaded_sphere", mat0, r, { color: rgba_hex_color(color0h) });
                    }


                    {
                        let mat0 = scale_mat4(400);
                        mat0 = mat4_mul(translation_mat4(sat_pos1), mat0);
                        mat0 = mat4_mul(mvp, mat0);
                        gl.draw_simple("shaded_sphere", mat0, r, { color: rgba_hex_color(color4h) });
                    }

                    {
                        let mat0 = scale_mat4(200);
                        mat0 = mat4_mul(translation_mat4(sat_pos2), mat0);
                        mat0 = mat4_mul(mvp, mat0);
                        gl.draw_simple("shaded_sphere", mat0, r, { color: rgba_hex_color(color2h) });
                    }
                }
                else {

                    if (!eclipse) {
                        followed_bodies = [m_pos];


                        if (!draw_sun && mode !== "sky26") {
                            let mat = scale_mat4(moon_radius);
                            gl.draw_simple("moon_simple", mat4_mul(moon_mat, mat), rot, {});
                        }

                    }

                    let light_dir = vec_neg(vec_norm(m_pos));

                    light_dir = mat3_mul_vec(mat3_invert(moon_rot), light_dir);



                    if (mode !== "sky28" && !eclipse) {
                        let outset = mode === "sky36" ? 1 : 1.5;

                        gl.set_color_write_enabled(false);
                        gl.draw_simple("sphere", mat4_mul(moon_mat, scale_mat4(moon_radius * outset)), rot, { color: [1, 0, 0, 1] });

                        gl.set_color_write_enabled(true);
                    }

                    if (draw_sun) {



                        if (eclipse) {

                            function f(v, a) { v = vec_norm(v); v.push(a); return v; }
                            let params;

                            let d0 = vec_norm(vec_sub(observer_pos, e_pos));
                            let d1 = vec_norm(vec_neg(observer_pos));
                            let dim = smooth_step(-0.02, 0.1, vec_dot(d0, d1));

                            if (mode === "sky30") {
                                params = {
                                    dim: dim,
                                    dir0: f([-30.0, -10.5, 3.5], 0.4),
                                    dir1: f([-30.0, -10.4, 4.1], 0.3),
                                    dir2: f([-39.0, 17.3, 6.1], 0.2),
                                }
                            } else {
                                params = {
                                    dim: dim,
                                    dir0: f([10, -2.5, -0.4], 0.3),
                                    dir1: f([11, -2.5, -0.3], 0.2),
                                    dir2: f([10, 1.8, 0.4], 0.2),
                                }
                            }

                            gl.draw_simple("sun_eclipse", mat4_mul(mvp, scale_mat4(sun_radius)), r, params);
                        } else {


                            let m = mat3_transpose(mat3_mul(earth_rot, local_mat));
                            let dir = vec_norm(mat3_mul_vec(m, vec_neg(observer_pos)));

                            let color = transmittance_color(dir, true);

                            gl.set_color_write_enabled(false);

                            gl.draw_simple("sphere", mat4_mul(mvp, scale_mat4(sun_radius * 1.5)), rot, { color: color });
 

                            gl.set_color_write_enabled(true);

                            {

                                let c = mat4_mul_vec3(mvp, [0, 0, 0]);

                                if (c[3] > 0) {
                                    c = vec_scale(c, 1 / c[3]);

                                    let size = dist * 0.016 * aspect;
                                    let options = {};
                                    options.mat = [size, size * width / height, c[0], c[1]];
                                    options.color = color;
                                    options.seed = (t - eph.eph_start_date) * 20;

                                    gl.draw_full("sun_rays", options);

                                }
                            }

                            // gl.draw_simple("sun_rays", mat4_mul(mvp, scale_mat4(sun_radius * 2.7)), r, { color: color });

                            gl.set_depth_test_enabled(false);
                            gl.draw_simple("sphere", mat4_mul(mvp, scale_mat4(sun_radius)), rot, { color: color });



                        }

                    }

                }

                gl.set_depth_test_enabled(false);
                gl.set_depth_write_enabled(false);


                {

                    if (draw_sun || eclipse || mode === "sky26") {

                        let mmat = scale_mat3(moon_radius);
                        mmat = mat3_mul(moon_rot, mmat);
                        mmat = mat3_invert(mmat);

                        let rr = mat3_transpose(r);

                        let m_camera_pos = mat3_mul_vec(rr, (camera_offset));
                        let m_screen_pos = mat3_mul_vec(rr, screen_pos);
                        let m_screen_up = mat3_mul_vec(rr, screen_up);
                        let m_screen_right = mat3_mul_vec(rr, screen_right);

                        m_camera_pos = vec_add(m_camera_pos, vec_sub(observer_pos, m_pos));
                        m_screen_pos = vec_add(m_screen_pos, vec_sub(observer_pos, m_pos));

                        m_camera_pos = mat3_mul_vec(mmat, m_camera_pos);
                        m_screen_pos = mat3_mul_vec(mmat, m_screen_pos);
                        m_screen_up = mat3_mul_vec(mmat, m_screen_up);
                        m_screen_right = mat3_mul_vec(mmat, m_screen_right);

                        let light_dir = vec_norm(mat3_mul_vec(mat3_transpose(moon_rot), (m_pos)));

                        light_dir.push(1);

                        let options = {
                            camera_pos: m_camera_pos,
                            screen_pos: m_screen_pos,
                            screen_up: m_screen_up,
                            screen_right: m_screen_right,
                            light_dir: light_dir,
                        };

                        let c = mat4_mul_vec3(mvp, m_pos);
                        c = vec_scale(c, 1 / c[3]);

                        let size = dist * 0.006 * aspect;
                        options.mat = [size, size * width / height, c[0], c[1]];

                        {

                            let m = mat3_transpose(mat3_mul(earth_rot, local_mat));
                            let local_sun_dir = vec_norm(mat3_mul_vec(m, vec_neg(observer_pos)));

                            let local_moon_dir = vec_norm(mat3_mul_vec(m, vec_sub(m_pos, observer_pos)));



                            let cos_lon = vec_dot(vec_norm(local_sun_dir.slice(0, 2)), vec_norm(local_moon_dir.slice(0, 2)));

                            let x = -cos_lon * 0.5 + 0.5;
                            x = sqrt(x);

                            let cos_lat = local_moon_dir[2];

                            let y = cos_lat;
                            y = 1.0 - y;
                            y = sqrt(y);

                            x = clamp(x, 0.0, 1.0);
                            y = clamp(y, 0.0, 1.0);

                            x = x * 255.0 / 256.0 + 0.5 / 256.0;
                            y = y * 255.0 / 256.0 + 0.5 / 256.0;


                            options.sky_dir = [x, y, cos_lat];

                            options.tint = transmittance_color(local_moon_dir);
                        }

                        if (mode === "sky26") {
                            options.tint = [1,1,1,1];
                        }

                        if (mode === "sky40") {
                            options.earthlight = 0.001;
                            options.light_dir[3] = 7;
                        }

                        if (draw_sun && !eclipse) {

                            let mat = scale_mat4(sun_radius * 1.4);
                            mat = mat4_mul(mvp, mat);
                        }

                        if (mode === "sky36") {

                            let sun_moon_pos = vec_neg(m_pos);
                            let inv_moon_rot = mat3_transpose(moon_rot);

                            let params = {};
                            params.earth = mat3_mul_vec(inv_moon_rot, vec_neg(moon_earth_pos));
                            params.sun = mat3_mul_vec(inv_moon_rot, sun_moon_pos);
                            let cov = vec_dot(vec_norm(params.earth), vec_norm(params.sun));
                            params.progress = smooth_step(0.99996, 0.99998, cov);
                            params.progress = 0.8 * params.progress * params.progress * params.progress;

                            let d = smooth_step(0.999965, 0.99997, cov) - smooth_step(0.99997, 0.999975, cov);
                            options.light_dir[3] = 1 + d;

                            gl.draw_full("complex_moon", options);

                            gl.set_blend_mode("multiply");
                            gl.draw_simple("moon_eclipse_light", mat4_mul(moon_mat, scale_mat4(moon_radius * 1.003)), ident_mat3, params);


                        } else if (mode !== "sky28") {

                            gl.set_blend_mode(eclipse ? "sover" : "plusl");

                            if (c[2] < 1)
                                gl.draw_full("complex_moon", options);
                        }
                        gl.set_blend_mode("sover");

                    }
                }

                if (mode === "sky28") {

                    let dir = vec_norm(vec_sub(m_pos, observer_pos));

                    let z = dir;
                    let x = vec_norm(vec_cross([0, 0, 1], z));
                    let y = vec_cross(z, x);


                    let ra = [
                        x[0], x[1], x[2],
                        y[0], y[1], y[2],
                        z[0], z[1], z[2],
                    ];
                    ra = mat3_transpose(ra);

                    let mat = mat3_to_mat4(ra);
                    mat = mat4_mul(translation_mat4(m_pos), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_ellipse(mat, ident_mat3, rgba_hex_color(color5h, 0.9), moon_radius, 0, 300);
                }

                gl.set_depth_test_enabled(false);


                if (!moon_locked && !sun_locked) {
                    let dir = vec_norm(local_observer_pos);
                    let zenith = vec_add(local_observer_pos, vec_scale(dir, 500000));
                    let nadir = vec_add(local_observer_pos, vec_scale(dir, -500000));

                    let north = [0, 0, 1];
                    let dir_ew = vec_norm(vec_cross(local_observer_pos, north));
                    let dir_ns = vec_norm(vec_cross(local_observer_pos, dir_ew));

                    let s = artifical_sats ? 640 : 320;
                    let h = artifical_sats ? 8000 : 4000;

                    gl.draw_segment(earth_mat, r, [0.1, 0.1, 0.1, 0.1],
                        vec_add(zenith, vec_scale(dir_ew, h)),
                        vec_add(zenith, vec_scale(dir_ew, -h)),
                        s);

                    gl.draw_segment(earth_mat, r, [0.1, 0.1, 0.1, 0.1],
                        vec_add(zenith, vec_scale(dir_ns, h)),
                        vec_add(zenith, vec_scale(dir_ns, -h)),
                        s);

                    gl.draw_segment(earth_mat, r, [0.1, 0.1, 0.1, 0.1],
                        vec_add(nadir, vec_scale(dir_ew, h)),
                        vec_add(nadir, vec_scale(dir_ew, -h)),
                        s);

                    gl.draw_segment(earth_mat, r, [0.1, 0.1, 0.1, 0.1],
                        vec_add(nadir, vec_scale(dir_ns, h)),
                        vec_add(nadir, vec_scale(dir_ns, -h)),
                        s);
                }


                // land
                {

                    let mat = ident_mat4;
                    mat = mat4_mul(mat3_to_mat4(local_mat), mat);
                    mat = mat4_mul(translation_mat4(vec_scale(local_observer_pos, 1)), mat);
                    mat = mat4_mul(earth_mat, mat);

                    let r = artifical_sats ? 10000 : 1000000;

                    if (has_land) {
                        gl.set_depth_write_enabled(true);

                        gl.draw_segment(mat, rot, eclipse ? [0, 0, 0, 1] : [0.02, 0.02, 0.02, 1], [0, 0, 0], [0, 0, -10000000], r);

                        let params = {};
                        params.color = [0, 0, 0, 1];
                        params.feather = 0.99;

                        let m = scale_mat4(1000);
                        m = mat4_mul(translation_mat4([0, 0, -2000]), m);
                        m = mat4_mul(mat, m);
                        gl.draw_simple("disc", m, rot, params);

                        gl.set_depth_write_enabled(false);
                    }

                    gl.set_depth_write_enabled(false);
                    gl.set_blend_enabled(true);

                    if (has_horizon) {

                        let c = [0.3, 0.37, 0.45, 1.0];

                        let d = vec_dot(vec_norm(e_pos), vec_norm(vec_sub(e_pos, observer_pos)));

                        if (!draw_sun)
                            d = 0;

                        c = vec_lerp(c, [0.1, 0.1, 0.1, 1.0], 1 - smooth_step(0, 0.1, d));

                        let params = {
                            color: c,
                            seed: [lat * 10, lon * 10]
                        }

                        gl.draw_horizon(mat, params);
                    }


                }


                gl.set_depth_test_enabled(true);


                if (artifical_sats) {

                    for (let i = 0; i < history_count; i++) {
                        let tt = lerp(trail_t0, trail_t1, i / history_count);

                        let moon_earth_pos = eph.moon_earth_pos(tt);
                        let emb_pos = eph.emb_pos(tt);
                        let e_pos = vec_scale(moon_earth_pos, -1 / (1 + earth_moon_mass_ratio));

                        let earth_rot = eph.earth_rot_mat(tt);
                        let inv_earth_rot = mat3_transpose(earth_rot);

                        let dir = mat3_mul_vec(inv_earth_rot, base_sat_pos0);
                        let dir2 = mat3_mul_vec(inv_earth_rot, base_sat_pos1);
                        let dir3 = mat3_mul_vec(inv_earth_rot, base_sat_pos2);


                        state.hist[i * 3 + 0] = dir[0];
                        state.hist[i * 3 + 1] = dir[1];
                        state.hist[i * 3 + 2] = dir[2];

                        state.hist[history_count * 3 + i * 3 + 0] = dir2[0];
                        state.hist[history_count * 3 + i * 3 + 1] = dir2[1];
                        state.hist[history_count * 3 + i * 3 + 2] = dir2[2];

                        state.hist[history_count * 6 + i * 3 + 0] = dir3[0];
                        state.hist[history_count * 6 + i * 3 + 1] = dir3[1];
                        state.hist[history_count * 6 + i * 3 + 2] = dir3[2];
                    }


                    gl.update_trail_buffer(state.hist);

                    gl.draw_trail(earth_mat, rot, 0, history_count, {
                        color: rgba_hex_color(color0h, 0.3),
                        alpha_range: [0, 1, history_count - 1, history_count]
                    });

                    gl.draw_trail(earth_mat, rot, history_count * 3, history_count, {
                        color: rgba_hex_color(color4h, 0.3),
                        alpha_range: [0, 1, history_count - 1, history_count]
                    });


                    gl.draw_trail(earth_mat, rot, history_count * 6, history_count, {
                        color: rgba_hex_color(color2h, 0.3),
                        alpha_range: [0, 1, history_count - 1, history_count]
                    });

                } else if (!moon_locked && !sun_locked) {


                    for (let i = 0; i < history_count; i++) {
                        let tt = lerp(trail_t0, trail_t1, i / (history_count - 1));

                        let moon_earth_pos = eph.moon_earth_pos(tt);
                        let emb_pos = eph.emb_pos(tt);
                        let e_pos = vec_scale(moon_earth_pos, -1 / (1 + earth_moon_mass_ratio));
                        let sun_earth_pos = vec_neg(vec_add(emb_pos, e_pos));

                        let earth_rot = eph.earth_rot_mat(tt);
                        let inv_earth_rot = mat3_transpose(earth_rot);

                        let dir = mat3_mul_vec(inv_earth_rot, moon_earth_pos);
                        let dir2 = mat3_mul_vec(inv_earth_rot, sun_earth_pos);


                        state.hist[i * 3 + 0] = dir[0];
                        state.hist[i * 3 + 1] = dir[1];
                        state.hist[i * 3 + 2] = dir[2];

                        state.hist[history_count * 3 + i * 3 + 0] = dir2[0];
                        state.hist[history_count * 3 + i * 3 + 1] = dir2[1];
                        state.hist[history_count * 3 + i * 3 + 2] = dir2[2];
                    }


                    gl.update_trail_buffer(state.hist);


                    gl.draw_trail(earth_mat, rot, 0, history_count, {
                        color: [0.3, 0.3, 0.3, 0.3],
                        alpha_range: [0, trail_alpha_range, history_count - trail_alpha_range - 1, history_count - 1]
                    });


                    if (draw_sun) {

                        gl.draw_trail(earth_mat, rot, history_count * 3, history_count, {
                            color: [0.1, 0.1, 0.1, 0.1],
                            alpha_range: [0, trail_alpha_range, history_count - trail_alpha_range, history_count]
                        });
                    }

                }


                if (mode === "sky36") {
                    let R = sun_radius;
                    let r = earth_radius;
                    let Rr = R - r;

                    let d = vec_len(e_pos);
                    let D = R * d / Rr;

                    let md = vec_len(moon_earth_pos);
                    let mr = R * (D - d - md) / D;

                    let mid = d * R / (R + r);
                    let mr2 = R * (md + d - mid) / mid;

                    let dir = vec_scale(e_pos, 1 / d);

                    let z = dir;
                    let x = vec_norm(vec_cross([0, 0, 1], z));
                    let y = vec_cross(z, x);


                    let ra = [
                        x[0], x[1], x[2],
                        y[0], y[1], y[2],
                        z[0], z[1], z[2],
                    ];
                    ra = mat3_transpose(ra);

                    let mat = mat3_to_mat4(ra);
                    mat = mat4_mul(translation_mat4(vec_add(e_pos, vec_scale(dir, md))), mat);
                    mat = mat4_mul(mvp, mat);


                    gl.set_depth_test_enabled(true);

                    gl.draw_ellipse(mat, ident_mat3, rgba_hex_color(color3h, 0.25), mr, 0, 18);

                    gl.draw_ellipse(mat, ident_mat3, rgba_hex_color(color1h, 0.25), mr2, 0, 18);


                }

                ctx.drawImage(gl.finish(), 0, 0, w, h);

                ctx.save();
                ctx.fillStyle = "red";
                ctx.translate(width / 2, height / 2);
                ctx.scale(width * 0.5, -width * 0.5);
                for (let pos of followed_bodies) {

                    let p = mat4_mul_vec3(mvp, pos);
                    let dd = p[3];
                    p = vec_scale(p, 1 / p[3]);

                    let dir = p.slice(0, 2);

                    if (dd < 0) {
                        let sc = dd / 10.0;
                        dir[0] *= sc;
                        dir[1] *= sc;
                    }

                    let as = height / width;

                    if (abs(dir[0]) > 1) {
                        dir = vec_scale(dir, 1 / abs(dir[0]));
                    }

                    if (abs(dir[1]) > 1) {
                        dir = vec_scale(dir, 1 / abs(dir[1]));
                    }

                    let a = 0.7 * smooth_step(0.8, 0.9, max(abs(dir[0]), abs(dir[1])));

                    if (a <= 0)
                        continue;

                    dir[1] *= as;


                    ctx.globalAlpha = a;
                    let norm_dir = vec_norm(dir);

                    norm_dir[1] *= as;


                    ctx.save();
                    ctx.translate(dir[0] - norm_dir[0] * 0.05, dir[1] - norm_dir[1] * 0.05);



                    ctx.transform(norm_dir[0], norm_dir[1], -norm_dir[1], norm_dir[0], 0, 0);

                    ctx.lineWidth = 0.004;

                    ctx.fillStyle = "#fff";
                    ctx.strokeStyle = "#333";

                    let len = 0.12;
                    ctx.arrow(-len, 0, 0, 0,
                        len * 0.16,
                        len * 0.45,
                        len * 0.55)

                    ctx.fill();
                    ctx.stroke();

                    ctx.restore();

                }
                ctx.restore();

                if (draw_outline) {
                    let ww = 5;
                    ctx.lineWidth = ww;


                    ctx.strokeStyle = color0;
                    ctx.strokeLine(0, 0, 0, h)

                    ctx.strokeStyle = color1;
                    ctx.strokeLine(w, 0, w, h)


                    ctx.lineJoin = "bevel";

                    ctx.strokeStyle = color3;

                    ctx.beginPath();
                    ctx.lineTo(ww / 2, 2 * h);
                    ctx.lineTo(ww / 2, h);
                    ctx.lineTo(w - ww / 2, h);
                    ctx.lineTo(w - ww / 2, 2 * h);
                    ctx.stroke();

                    ctx.strokeStyle = color2;


                    ctx.beginPath();
                    ctx.lineTo(ww / 2, -h);
                    ctx.lineTo(ww / 2, 0);
                    ctx.lineTo(w - ww / 2, 0);
                    ctx.lineTo(w - ww / 2, -h);
                    ctx.stroke();

                } else if (mode !== "sky13" && mode !== "sky13a") {
                    let w = canvas.height * 0.03;
                    ctx.feather(width * scale, height * scale, w, w, w, w);
                }

                ctx.fillStyle = "#fff";

                if (mode !== "sky13" && mode !== "sky13a" && mode !== "sky26" && mode !== "sky40") {
                    ctx.globalAlpha = 0.5 * smooth_step(-0.05, 0.1, rot[8]);


                    ctx.fillText("below the horizon", width * 0.5, height - font_size * (sun_locked || moon_locked ? 0.5 : 2.0));
                }

                if (!sun_locked && !moon_locked) {
                    let x_fov = 2 * Math.atan(1 / dist);

                    let offset_per_rad = width / x_fov;

                    let a = atan2(rot[1], rot[0]);

                    ctx.globalAlpha = 0.5 * smooth_step(0.4, 0.8, rot[5]);

                    let dirs = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"];
                    for (let i = -8; i < 16; i++) {

                        let ii = (i + 8) & 7;
                        let x = width * 0.5 + (a + pi / 4 * i) * offset_per_rad;
                        ctx.fillText(dirs[ii], x, height - font_size * 0.5);
                    }

                }

                ctx.globalAlpha = 1;


                if (!artifical_sats && mode !== "sky40" && mode !== "sky26") {
                    let offset = mode.startsWith("sky13") ? -10 : 0;

                    let colored = mode === "sky1" || mode === "sky2" || mode === "sky20" || mode === "sky23";
                    draw_date_and_time(width * 0.97 + offset, width * 0.03, t, colored, mode !== "sky28");
                }

                if (mode === "sky13") {
                    ctx.fillStyle = color1;
                    ctx.textAlign = "right";
                    ctx.fillText("apoapsis", width * 0.9, height - font_size);
                } else if (mode === "sky13a") {
                    ctx.fillStyle = color3;
                    ctx.textAlign = "left";
                    ctx.fillText("periapsis", width * 0.1, height - font_size);

                    ctx.strokeStyle = "rgba(255,255,255,0.15)"
                    ctx.strokeLine(0.5, 0, 0.5, height);
                }

                if (mode === "sky26") {
                    let emb_vel = eph.emb_vel(t);
                    let ecliptic_p_z = vec_norm(vec_cross(emb_pos, emb_vel));


                    ctx.fillStyle = "white";
                    ctx.translate(width / 2, height - font_size);
                    draw_moon_phase_label(m_pos, e_pos, ecliptic_p_z);
                }


            }


            else if (mode.startsWith("m_orbit") || mode.startsWith("em_orbit")) {

                if (!eph)
                    return;

                let time_scale = 500000.0;
                let fixed_trail = true;

                let t0 = global_start_t;


                let history_count = trail_history_count / 2;
                if (mode.startsWith("m_orbit")) {
                    time_scale = 100000.0;
                    history_count = trail_history_count / 4;

                    if (mode === "m_orbit3") {
                        time_scale *= 5;
                        history_count = trail_history_count / 16;
                    }
                }
                else if (mode === "em_orbit1") {
                    history_count = trail_history_count;
                } else if (mode === "em_orbit5" || mode === "em_orbit6") {
                    time_scale = 200000.0;
                } else if (mode === "em_orbit7") {
                    time_scale = 200000.0;
                    t0 -= 1000;
                } else if (mode === "em_orbit6a") {
                    time_scale = 0.0;
                } else if (mode === "em_orbit7a") {
                    t0 -= 1000;
                    time_scale = 1600000.0;
                    history_count = trail_history_count * 1 / 8;
                } else if (mode === "em_orbit9") {
                    time_scale = 1600000.0;
                    history_count = trail_history_count * 1 / 8;
                }


                if (!state) {
                    state = {};
                    state.t = t0;

                    state.hist = new Float32Array(history_count * 3 * 3);
                    state.hist.fill(NaN);
                    state.hist_i = 0;
                    state.hist_t = 0;
                } else if (mode === "em_orbit12") {
                    time_scale = 2000000.0;
                } else if (mode === "em_orbit22") {
                    time_scale = 200000.0;
                } else if (mode === "em_orbit25") {
                    time_scale = 0.0;
                }

                if (mode.startsWith("m_orbit"))
                    time_scale *= slider_args[0] * slider_args[0];
                else
                    time_scale *= slider_args[1] * slider_args[1];


                dt *= time_scale / 3600 / 24;

                state.t += dt;

                if (state.t >= eph.eph_end_date) {
                    state.t = eph.eph_start_date;
                }

                let trail_t0 = state.t - 26;
                let trail_t1 = state.t;
                let trail_alpha_range = 50;

                let base_t = state.t;

                if (mode === "m_orbit5") {
                    base_t = 2460639.817;
                    state.t = base_t + slider_args[0];

                    trail_t0 = state.t - 26.50;
                    trail_t1 = state.t;

                    fixed_trail = true;

                } else if (mode === "m_orbit7") {
                    state.t = eph_start_date + 10 + slider_args[1] * 2;
                } else if (mode === "m_orbit8" || mode === "m_orbit9") {
                    let base_t = 2451536.5 + 9104.498;
                    state.t = base_t + slider_args[0] * 27.812;

                    trail_t0 = base_t - 0.0;
                    trail_t1 = state.t;

                    fixed_trail = true;
                } else if (mode === "em_orbit6a") {
                    let base_t = 2460379.88;
                    state.t = base_t + slider_args[1] * 29.393;

                    trail_t0 = state.t - 26.50;
                    trail_t1 = state.t;

                    fixed_trail = true;

                } else if (mode === "em_orbit25") {

                    let t = lerp(JD(2024, 12, 30 + (22 + 27 / 60) / 24), JD(2025, 1, 29 + (12 + 36 / 60) / 24), slider_args[1]);

                    state.t = t;
                    trail_t0 = t - 26.50;
                    trail_t1 = t;
                    fixed_trail = true;
                }

                let t = state.t;

                let emb_pos = eph.emb_pos(t);
                let emb_vel = eph.emb_vel(t);

                let moon_earth_pos = eph.moon_earth_pos(t);
                let moon_earth_vel = eph.moon_earth_vel(t);

                let e_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, -1 / (1 + earth_moon_mass_ratio)));
                let m_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, earth_moon_mass_ratio / (1 + earth_moon_mass_ratio)));

                let earth_rot = eph.earth_rot_mat(t);
                let moon_rot = eph.moon_rot_mat(t);

                let ecliptic_p_x = vec_norm(emb_pos);
                let ecliptic_p_z = vec_norm(vec_cross(emb_pos, emb_vel));
                let ecliptic_p_y = vec_cross(ecliptic_p_x, ecliptic_p_z);


                let orbit_p_z = vec_norm(vec_cross(moon_earth_pos, moon_earth_vel));


                let line_of_nodes_dir = vec_norm(vec_cross(orbit_p_z, ecliptic_p_z));
                let orbit_p_x = line_of_nodes_dir;
                let orbit_p_y = vec_cross(orbit_p_z, orbit_p_x);

                let omega;

                {
                    let plane_x = vec_norm(vec_cross([0, 1, 0], ecliptic_p_z));


                    omega = acos(vec_dot(plane_x, line_of_nodes_dir));
                    omega = pi - omega;

                    if (vec_dot(vec_cross(plane_x, line_of_nodes_dir), ecliptic_p_z) > 0)
                        omega = 2 * pi - omega;
                }

                let e_inclination_angle = acos(vec_dot(mat3_mul_vec(earth_rot, [0, 0, 1]), ecliptic_p_z));
                let m_inclination_angle = acos(vec_dot(mat3_mul_vec(moon_rot, [0, 0, 1]), ecliptic_p_z));


                let line_of_nodes_length = 430000;

                let w = width;
                let h = width;

                let dist = 10;
                let screen_pos = [0, 0, 1700000000];
                let screen_up = [0, 1, 0];
                let screen_right = [1, 0, 0];

                let emb_size = 2500000;
                let emb_alpha = 1.0;

                let thin_r = 350000;
                let mid_r = 420000;
                let thick_r = 1000000;

                let planet_sc = smooth_lerp(1, 10, planet_scale);

                let screen_off = [0, 0, 0];

                let trail_reference = [0, 0, 0];
                let e_referenced = false;
                let sun_referenced = true;
                let emb_referenced = false;

                let e_axis_a = 1;
                let m_axis_a = 1;

                let emb_x_axis_a = 0;
                let ecliptic_x_axis_a = 0;

                let near = 1e6;
                let far = 1e10;

                let draw_sun = true;
                let draw_emb_trail = true;
                let draw_e = true;
                let draw_e_trail = true;
                let draw_m = true;
                let draw_m_trail = true;

                let draw_ecliptic = true;
                let draw_line_of_nodes = false;
                let draw_to_sun_dir = false;
                let draw_to_reference_dir = false;

                let big_m_axis = false;
                let big_e_axis = false;

                let orbital_a = 1.0;
                let m_orbital_ellipse_a = 0.0;
                let m_trail_a = 0.2;

                let em_orbit_center = emb_pos;

                let m_cone_a = 0;

                let apsides_a = 0.0;



                let line_of_nodes_angle_a = 0;
                let inclination_a = 0;
                let show_date = true;

                const anomalistic_markers_count = 128;


                let feather_scale = 0;

                let sunlight = false;




                let r = rot;
                let hist_step = 0.2;

                let zoom_scale = 1.0;
                let zoom_t = 1.0;

                if (mode.startsWith("m_orbit")) {

                    let plane_z = orbit_p_z;
                    let plane_x = vec_norm(vec_cross(orbit_p_z, [0, 1, 0]));

                    if (mode === "m_orbit4a" || mode === "m_orbit5") {
                        plane_z = mat3_mul_vec(earth_rot, [0, 0, 1]);
                        plane_x = vec_norm(vec_cross(plane_z, [0, 1, 0]));
                    } else
                        if (mode === "m_orbit7" || mode === "m_orbit8" || mode === "m_orbit9") {
                            plane_x = vec_norm(moon_earth_pos);
                        }

                    let plane_y = vec_cross(plane_z, plane_x);
                    let plane_mat = [
                        plane_x[0], plane_x[1], plane_x[2],
                        plane_y[0], plane_y[1], plane_y[2],
                        plane_z[0], plane_z[1], plane_z[2]];

                    r = mat3_mul(r, plane_mat);

                    trail_reference = e_pos;
                    e_referenced = true;

                    em_orbit_center = e_pos;

                    hist_step = 0.025;
                    orbital_a = 0;

                    draw_sun = false;
                    draw_ecliptic = false;
                    draw_line_of_nodes = false;
                    draw_emb_trail = false;



                    near = 1e4;
                    far = 1e10;

                    let t = slider_args[0];


                    let base_d = 4300000;
                    let end_d = 300000;

                    let offset_t = 0;
                    e_axis_a = 1;
                    m_axis_a = 1;

                    zoom_t = 0;

                    emb_size = earth_radius * 0.06;
                    emb_alpha = 0.0;

                    emb_x_axis_a = 1;
                    if (mode === "m_orbit1") {
                        orbital_a = 1.0

                    } else if (mode === "m_orbit2" || mode === "m_orbit3") {
                        m_orbital_ellipse_a = 1;
                        m_trail_a = 0.3;
                        apsides_a = 1.0;
                    } else if (mode === "m_orbit4") {
                        orbital_a = 1.0;
                    } else if (mode === "m_orbit4a" || mode === "m_orbit5") {
                        emb_x_axis_a = 0;
                        orbital_a = 1.0;
                    } else if (mode === "m_orbit8") {
                        m_orbital_ellipse_a = 1;
                        apsides_a = 1;
                        m_cone_a = 1;
                    } else if (mode === "m_orbit9") {
                        m_cone_a = 1;
                    }

                    zoom_t = zoom_t * zoom_t;
                    zoom_t = smooth_step(0, 1, zoom_t);


                    let pos = Math.exp(lerp(Math.log(base_d), Math.log(end_d), zoom_t))

                    let sc = pos / base_d;

                    zoom_scale = sc;

                    thin_r *= sc * 0.003;
                    mid_r *= sc * 0.003;
                    thick_r *= sc * 0.003;

                    let center_t = 1.0 - sc
                    center_t += sc * zoom_t;

                    zoom_t = (pos - end_d) / (base_d - end_d)

                    screen_pos = [0, 0, pos];
                    screen_off = vec_scale(vec_sub(m_pos, e_pos), -center_t * offset_t);

                    screen_off = vec_add(screen_off, vec_scale(e_pos, -1));
                }
                else {


                    let plane_z = ecliptic_p_z;
                    let plane_x = vec_norm(vec_cross(ecliptic_p_z, [0, 1, 0]));



                    let t = slider_args[0];

                    let base_d = 1900000000;
                    let end_d = 5000000;

                    let pos = Math.exp(lerp(Math.log(base_d), Math.log(end_d), t))

                    let sc = pos / base_d;

                    zoom_t = (pos - end_d) / (base_d - end_d);

                    zoom_scale = sc;
                    thin_r *= sc;
                    mid_r *= sc;
                    thick_r *= sc;

                    let center_t = 1.0 - sc
                    center_t += sc * t;

                    emb_size *= sc;

                    let target = emb_pos;

                    emb_referenced = true;
                    draw_m_trail = draw_e_trail = true;
                    trail_reference = emb_pos;

                    let closeup_a = 1.0 - smooth_step(0.1, 0.4, pos / base_d);

                    if (mode === "em_orbit1") {
                        trail_reference = [0, 0, 0];
                        emb_referenced = false;

                        trail_t0 = state.t - 350;
                        emb_alpha = 0.0;
                        draw_emb_trail = draw_ecliptic = false;
                        orbital_a = 0;
                    } else if (mode === "em_orbit2") {
                        trail_reference = [0, 0, 0];
                        emb_referenced = false;

                        trail_t0 = state.t - 350;
                        draw_m_trail = draw_e_trail = false;
                        orbital_a = 0;
                    } else if (mode === "em_orbit5") {


                        inclination_a = closeup_a;
                    } else if (mode === "em_orbit6") {

                        draw_line_of_nodes = true;
                    } else if (mode === "em_orbit6a") {

                        emb_alpha = 0;
                        draw_line_of_nodes = true;
                        sunlight = true;

                        draw_to_sun_dir = true;
                    }
                    else if (mode === "em_orbit7" || mode === "em_orbit7a") {

                        emb_referenced = true;
                        draw_m_trail = draw_e_trail = true;
                        trail_reference = emb_pos;

                        ecliptic_x_axis_a = 1;
                        draw_line_of_nodes = true;

                        line_of_nodes_angle_a = closeup_a;
                    } else if (mode === "em_orbit8") {
                        big_m_axis = true;
                        big_e_axis = true;
                    } else if (mode === "em_orbit9") {
                        big_m_axis = true;
                        big_e_axis = true;
                        draw_line_of_nodes = true;

                    } else if (mode === "em_orbit10") {
                        big_m_axis = true;

                    } else if (mode === "em_orbit12") {
                        plane_z = mat3_mul_vec(earth_rot, [0, 0, 1]);
                        plane_x = vec_norm(vec_cross(plane_z, orbit_p_z));
                        draw_ecliptic = false;
                        target = e_pos;
                        big_e_axis = true;
                    } else if (mode === "em_orbit20" || mode === "em_orbit22" || mode === "em_orbit25") {
                        sunlight = true;
                        draw_to_sun_dir = true;
                        orbital_a = 0;
                        draw_ecliptic = false;
                        draw_emb_trail = false;
                        emb_alpha = 0.0;
                        emb_referenced = false;
                        trail_reference = [0, 0, 0];
                        trail_t0 = state.t - 350;


                        if (mode === "em_orbit22")
                            draw_to_reference_dir = true;
                        if (mode === "em_orbit25") {
                            m_cone_a = 1;
                            sunlight = true;
                        }
                    } else if (mode === "m_orbit8" || mode === "m_orbit9" || mode === "em_orbit12") {
                        draw_m_trail = draw_e_trail = true;
                    } else if (mode === "em_orbit30") {
                        sunlight = true;
                        orbital_a = 0;
                        draw_ecliptic = false;
                        draw_emb_trail = false;
                        emb_alpha = 0.0;
                        draw_m_trail = draw_e_trail = false;


                    } else if (mode === "em_orbit50") {
                        sunlight = true;
                        orbital_a = 0;
                        draw_ecliptic = false;
                        draw_emb_trail = false;
                        emb_referenced = false;
                        trail_reference = [0, 0, 0];
                        trail_t0 = state.t - 350;
                        emb_alpha = 0.0;
                    }


                    let plane_y = vec_cross(plane_z, plane_x);
                    let plane_mat = [
                        plane_x[0], plane_x[1], plane_x[2],
                        plane_y[0], plane_y[1], plane_y[2],
                        plane_z[0], plane_z[1], plane_z[2]];

                    r = mat3_mul(r, plane_mat);



                    screen_pos = [0, 0, pos];
                    screen_off = vec_scale(target, -center_t);
                    feather_scale = 1;
                }



                let front = vec_cross(screen_up, screen_right);
                let camera_offset = vec_sub(screen_pos, vec_scale(front, dist));

                let f = dist;
                near = 1e7;
                far = 1e12;
                let rangeInv = 1 / (near - far);

                let proj = [
                    f, 0, 0, 0,
                    0, f, 0, 0,
                    0, 0, (near + far) * rangeInv, near * far * rangeInv * 2,
                    0, 0, -0.6, 1
                ];

                let proj_w = 0.1 * camera_offset[2];
                let proj_h = proj_w;


                proj = [
                    1 / proj_w, 0, 0, 0,
                    0, 1 / proj_h, 0, 0,
                    0, 0, -1e-9, 0,
                    0, 0, 0, 1
                ];


                let mvp = mat4_mul(proj, mat3_to_mat4(r));
                mvp = mat4_mul(mvp, translation_mat4(screen_off));


                let earth_mat = mat3_to_mat4(earth_rot);
                earth_mat = mat4_mul(translation_mat4(e_pos), earth_mat);
                earth_mat = mat4_mul(mvp, earth_mat);

                let moon_mat = mat3_to_mat4(moon_rot);
                moon_mat = mat4_mul(translation_mat4(m_pos), moon_mat);
                moon_mat = mat4_mul(mvp, moon_mat);



                let moon_orbit_args;

                if (m_orbital_ellipse_a > 0 || apsides_a > 0 || draw_line_of_nodes) {

                    function moon_args(t) {
                        let moon_earth_pos = eph.moon_earth_pos(t);
                        let moon_earth_vel = eph.moon_earth_vel(t);

                        let p = vec_scale(moon_earth_pos, 1000.0);
                        let v = vec_scale(moon_earth_vel, 1000.0);
                        let r = vec_len(p);

                        let mu = G * (earth_mass + moon_mass);
                        let h = vec_cross(p, v);
                        let e = vec_sub(vec_scale(vec_cross(v, h), 1 / mu), vec_scale(p, 1 / r));
                        let ee = vec_len(e);
                        let a = 1 / (2 / r - vec_dot(v, v) / mu);
                        let omega = atan2(vec_dot(vec_norm(e), orbit_p_y), vec_dot(vec_norm(e), orbit_p_x));
                        let ta = omega - atan2(vec_dot(vec_norm(p), orbit_p_y), vec_dot(vec_norm(p), orbit_p_x));


                        if (ta > pi)
                            ta -= 2 * pi;

                        if (ta < -pi)
                            ta += 2 * pi;


                        let res = {};

                        res.a = a * 0.001;
                        res.e = ee;
                        res.argp = omega;
                        res.ta = ta;

                        return res;
                    }

                    moon_orbit_args = moon_args(t);

                    if (mode === "m_orbit3" && state.moon_ta > 0 && moon_orbit_args.ta <= 0) {
                        if (!state.anomalistic_markers) {
                            state.anomalistic_markers = [];
                            state.anomalistic_markers_i = 0;
                        }

                        let tt = bisect(state.last_t, t, function (t) {
                            return moon_args(t).ta;
                        });

                        let pp = eph.moon_earth_pos(tt);
                        state.anomalistic_markers.push(pp);

                        if (state.anomalistic_markers.length > anomalistic_markers_count) {
                            state.anomalistic_markers.shift();
                            state.anomalistic_markers_i++;
                        }
                    }

                    state.last_t = t;
                    state.moon_ta = moon_orbit_args.ta;
                }

                if (fixed_trail) {

                    for (let i = 0; i < history_count; i++) {
                        let tt = lerp(trail_t0, trail_t1, i / (history_count - 1));

                        let moon_earth_pos = eph.moon_earth_pos(tt);
                        let emb_pos = eph.emb_pos(tt);

                        let e_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, -1 / (1 + earth_moon_mass_ratio)));
                        let m_pos = vec_add(emb_pos, vec_scale(moon_earth_pos, earth_moon_mass_ratio / (1 + earth_moon_mass_ratio)));

                        let p = [0, 0, 0];
                        if (e_referenced)
                            p = e_pos;
                        else if (emb_referenced)
                            p = emb_pos;

                        state.hist[i * 3 + 0] = emb_pos[0] - p[0];
                        state.hist[i * 3 + 1] = emb_pos[1] - p[1];
                        state.hist[i * 3 + 2] = emb_pos[2] - p[2];

                        state.hist[(i + history_count) * 3 + 0] = e_pos[0] - p[0];
                        state.hist[(i + history_count) * 3 + 1] = e_pos[1] - p[1];
                        state.hist[(i + history_count) * 3 + 2] = e_pos[2] - p[2];

                        state.hist[(i + history_count * 2) * 3 + 0] = m_pos[0] - p[0];
                        state.hist[(i + history_count * 2) * 3 + 1] = m_pos[1] - p[1];
                        state.hist[(i + history_count * 2) * 3 + 2] = m_pos[2] - p[2];
                    }

                }


                if (sunlight) {
                    gl.create_transmittance_lut();
                }

                gl.begin(w, h);
                gl.set_depth_test_enabled(true);



                if (draw_m) {
                    let mat = scale_mat4(moon_radius * planet_sc);
                    let light_dir = vec_scale(vec_norm(m_pos), -1);
                    light_dir = mat3_mul_vec(mat3_invert(moon_rot), light_dir);
                    gl.draw_simple(sunlight ? "moon" : "moon_simple", mat4_mul(moon_mat, mat), rot, { light_dir });
                }





                if (draw_sun) {
                    let mat = mat4_mul(mvp, scale_mat4(sun_radius * planet_sc));
                    gl.draw_simple("sphere", mat, rot, { color: [1, 1, 0.9, 1.0] });
                }


                if (draw_e) {

                    let rot_a = 2 * Math.PI * 1.00273781191135448 * dt;

                    let mat = scale_mat4(earth_radius * planet_sc);
                    let light_dir = vec_scale(vec_norm(e_pos), -1);
                    light_dir = mat3_mul_vec(mat3_invert(earth_rot), light_dir);
                    gl.draw_simple(sunlight ? "earth" : "earth_simple", mat4_mul(earth_mat, mat), rot, { light_dir, blur: 0.1 * rot_a });
                }

                if (mode === "em_orbit50") {

                    let w = 800000 * zoom_scale;
                    let a = 0.3;


                    let plane_x = vec_norm(vec_sub(e_pos, m_pos));
                    let plane_z = vec_norm(vec_cross(m_pos, plane_x));
                    let plane_y = vec_cross(plane_x, plane_z);

                    let span = acos(vec_dot(plane_x, vec_norm(m_pos))) - pi;

                    let plane_mat = [
                        plane_x[0], plane_x[1], plane_x[2],
                        plane_y[0], plane_y[1], plane_y[2],
                        plane_z[0], plane_z[1], plane_z[2]];

                    plane_mat = mat3_transpose(plane_mat);

                    let mat = mat3_to_mat4(plane_mat);
                    mat = mat4_mul(translation_mat4(m_pos), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_ellipse(mat, ident_mat3, rgba_hex_color(color1h), 2.0e5, 0, 1000000 * zoom_scale, span);

                    let arrow_scale = 7000;
                    let d = (vec_len(moon_earth_pos) - earth_radius * planet_sc - arrow_scale * 12);
                    for (let i = 0; i < 2; i++) {

                        let arrow_dist = i == 0 ? d : d * 1.02;

                        let params = {};
                        params.color = rgba_hex_color(i == 0 ? color2h : color0h);

                        let mat = scale_mat4([-1, 1, 1]);
                        mat = mat4_mul(rot_y_mat4(-pi / 2), mat);
                        mat = mat4_mul(scale_mat4(arrow_scale), mat);
                        mat = mat4_mul(translation_mat4([arrow_dist, 0, 0]), mat);
                        mat = mat4_mul(rot_z_mat4(i == 0 ? 0 : span), mat);
                        mat = mat4_mul(mat3_to_mat4(plane_mat), mat);
                        mat = mat4_mul(translation_mat4(m_pos), mat);
                        mat = mat4_mul(mvp, mat);

                        let rr = ident_mat3.slice();
                        rr[0] *= -1;
                        rr = mat3_mul(rot_y_mat3(-pi / 2), rr);
                        rr = mat3_mul(rot_z_mat3(i == 0 ? 0 : span), rr);
                        rr = mat3_mul(plane_mat, rr);
                        rr = mat3_mul(r, rr);

                        gl.draw_simple("arrow", mat, rr, params);
                    }


                    gl.draw_segment(mvp, rot, rgba_hex_color(color2h, a), m_pos, vec_add(m_pos, vec_scale(vec_norm(moon_earth_pos), -d * 0.95)), w);

                    gl.draw_segment(mvp, rot, rgba_hex_color(color0h, a), m_pos, vec_add(m_pos, vec_scale(vec_norm(m_pos), -d * 0.95)), w);

                }


                let orbit_rot = [
                    orbit_p_x[0], orbit_p_y[0], orbit_p_z[0],
                    orbit_p_x[1], orbit_p_y[1], orbit_p_z[1],
                    orbit_p_x[2], orbit_p_y[2], orbit_p_z[2]];

                let ecliptic_rot = [
                    ecliptic_p_x[0], ecliptic_p_y[0], ecliptic_p_z[0],
                    ecliptic_p_x[1], ecliptic_p_y[1], ecliptic_p_z[1],
                    ecliptic_p_x[2], ecliptic_p_y[2], ecliptic_p_z[2]];

                if (mode === "m_orbit4" || mode === "m_orbit4a" || mode === "m_orbit5" || mode === "m_orbit9" || mode === "em_orbit22") {

                    let arrow_scale = 5000 * zoom_scale;

                    if (mode === "em_orbit22")
                        arrow_scale *= 300;

                    let params = {};
                    params.color = rgba_hex_color(0x3F86D2);

                    if (mode === "m_orbit4" || mode === "m_orbit4a" || mode === "m_orbit5" || mode === "em_orbit22") {
                        let mat = translation_mat4([0, 0, 13]);
                        mat = mat4_mul(scale_mat4(arrow_scale), mat);
                        mat = mat4_mul(rot_y_mat4(pi / 2), mat);
                        mat = mat4_mul(translation_mat4([earth_radius * planet_sc, 0, 0]), mat);
                        mat = mat4_mul(earth_mat, mat);

                        let r2 = rot_y_mat3(pi / 2);
                        r2 = mat3_mul(earth_rot, r2);
                        r2 = mat3_mul(r, r2);

                        gl.draw_simple("arrow", mat, r2, params);
                    }

                    params.color = rgba_hex_color(0xaaaaaa);

                    {
                        let mat = translation_mat4([0, 0, 13]);
                        mat = mat4_mul(scale_mat4(arrow_scale), mat);
                        mat = mat4_mul(rot_y_mat4(pi / 2), mat);
                        mat = mat4_mul(translation_mat4([moon_radius * planet_sc, 0, 0]), mat);
                        mat = mat4_mul(moon_mat, mat);

                        let r2 = rot_y_mat3(pi / 2);
                        r2 = mat3_mul(moon_rot, r2);
                        r2 = mat3_mul(r, r2);

                        gl.draw_simple("arrow", mat, r2, params);
                    }


                    gl.set_blend_enabled(true);
                    gl.set_depth_write_enabled(false);

                    gl.draw_segment(mvp, r, [0.1, 0.1, 0.1, 0.1], m_pos, e_pos, 800 * zoom_scale);


                    if (mode === "m_orbit5") {
                        let t = base_t;
                        let emb_pos2 = eph.emb_pos(t);
                        let moon_earth_pos2 = eph.moon_earth_pos(t);
                        let e_pos2 = vec_add(emb_pos2, vec_scale(moon_earth_pos2, -1 / (1 + earth_moon_mass_ratio)));
                        let m_pos2 = vec_add(emb_pos2, vec_scale(moon_earth_pos2, earth_moon_mass_ratio / (1 + earth_moon_mass_ratio)));

                        m_pos2 = vec_add(e_pos, vec_sub(m_pos2, e_pos2));

                        gl.draw_segment(mvp, r, [0.1, 0.1, 0.1, 0.1], m_pos2, e_pos, 800 * zoom_scale);
                    }
                }

                if (draw_line_of_nodes) {



                    let rot_mat = rot_z_mat3(moon_orbit_args.argp);
                    rot_mat = mat3_mul(orbit_rot, rot_mat);

                    let periapsis_dir = mat3_mul_vec(rot_mat, [1, 0, 0]);

                    let a = moon_orbit_args.a;
                    let ecc = moon_orbit_args.e;

                    let cos_a = vec_dot(line_of_nodes_dir, periapsis_dir);
                    let sin_a = -sqrt(1.0 - cos_a * cos_a);

                    if (vec_dot(orbit_p_z, vec_cross(line_of_nodes_dir, periapsis_dir)) < 0)
                        sin_a = -sin_a;

                    let r0 = a * (1 - ecc * ecc) / (1 + ecc * cos_a) * (earth_moon_mass_ratio - 1) / (earth_moon_mass_ratio);
                    let r1 = a * (1 - ecc * ecc) / (1 - ecc * cos_a) * (earth_moon_mass_ratio - 1) / (earth_moon_mass_ratio);


                    let p0 = [r0 * cos_a, r0 * sin_a, 0];
                    let p1 = [-r1 * cos_a, -r1 * sin_a, 0];

                    let base_mat = mat3_to_mat4(rot_mat);
                    base_mat = mat4_mul(translation_mat4(emb_pos), base_mat);
                    base_mat = mat4_mul(mvp, base_mat);

                    let mat0 = scale_mat4(6000);
                    mat0 = mat4_mul(translation_mat4(p0), mat0);
                    mat0 = mat4_mul(base_mat, mat0);

                    let mat1 = scale_mat4(6000);
                    mat1 = mat4_mul(translation_mat4(p1), mat1);
                    mat1 = mat4_mul(base_mat, mat1);


                    gl.draw_simple("sphere", mat0, ident_mat3, { color: rgba_hex_color(0xEA5644) });
                    gl.draw_simple("sphere", mat1, ident_mat3, { color: rgba_hex_color(0x6EAF38) });
                }

                if (state.anomalistic_markers) {

                    let i = 0;
                    for (let marker of state.anomalistic_markers) {

                        let alpha = 0.8 * smooth_step(0, anomalistic_markers_count / 4, anomalistic_markers_count - state.anomalistic_markers.length + i);

                        let mat = scale_mat4(4000);
                        mat = mat4_mul(translation_mat4(vec_add(e_pos, marker)), mat);
                        mat = mat4_mul(mvp, mat);

                        gl.draw_simple("sphere", mat, ident_mat3, { color: rgba_hex_color(0xEA5644, alpha) });
                        i++;
                    }
                }

                let orbit_p_z_earth_axis_angle;

                if (mode === "em_orbit10") {
                    let size = 1000000 * zoom_scale;
                    let length = 100000000 * zoom_scale;

                    let ecliptic0 = vec_add(m_pos, vec_scale(ecliptic_p_z, length));
                    let ecliptic1 = vec_sub(m_pos, vec_scale(ecliptic_p_z, length));

                    gl.draw_segment(mvp, rot, rgba_hex_color(color3h), ecliptic0, ecliptic1, size);

                    let plane0 = vec_add(m_pos, vec_scale(orbit_p_z, length));
                    let plane1 = vec_sub(m_pos, vec_scale(orbit_p_z, length));
                    gl.draw_segment(mvp, rot, rgba_hex_color(0x555555), plane0, plane1, size);
                } else if (mode === "em_orbit12") {
                    let size = 1000000 * zoom_scale;
                    let length = 100000000 * zoom_scale;
                    let plane0 = vec_add(e_pos, vec_scale(orbit_p_z, length));
                    let plane1 = vec_sub(e_pos, vec_scale(orbit_p_z, length));
                    gl.draw_segment(mvp, rot, rgba_hex_color(0x555555), plane0, plane1, size);

                    let axis = mat3_mul_vec(earth_rot, [0, 0, 1]);

                    let plane_x = axis;
                    let plane_z = vec_norm(vec_cross(axis, orbit_p_z));
                    let plane_y = vec_cross(plane_z, plane_x);


                    let a = acos(vec_dot(axis, orbit_p_z));
                    orbit_p_z_earth_axis_angle = a;

                    let plane_mat = [
                        plane_x[0], plane_x[1], plane_x[2],
                        plane_y[0], plane_y[1], plane_y[2],
                        plane_z[0], plane_z[1], plane_z[2]];

                    plane_mat = mat3_transpose(plane_mat);

                    let mat = mat3_to_mat4(plane_mat);
                    mat = mat4_mul(translation_mat4(e_pos), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_ellipse(mat, r, rgba_hex_color(color0h), 90000000 * zoom_scale * 0.9, 0, thick_r, a);

                    let a_min = 0.316560779996631;
                    let a_max = 0.501278032094095;

                    gl.draw_ellipse(mat, r, rgba_hex_color(color0h, 0.1), 80000000 * zoom_scale * 0.9, 0, thick_r * 0.7, a_min);
                    gl.draw_ellipse(mat, r, rgba_hex_color(color0h, 0.1), 100000000 * zoom_scale * 0.9, 0, thick_r * 0.7, a_max);

                    gl.draw_segment(mat4_mul(mat, rot_z_mat4(a_min)), rot, rgba_hex_color(0x555555, 0.2), [0, 0, 0], [100000000 * zoom_scale, 0, 0], size * 0.7);
                    gl.draw_segment(mat4_mul(mat, rot_z_mat4(a_max)), rot, rgba_hex_color(0x555555, 0.2), [0, 0, 0], [100000000 * zoom_scale, 0, 0], size * 0.7);


                }




                if (m_orbital_ellipse_a > 0 || apsides_a > 0) {

                    let base_mat = rot_z_mat4(moon_orbit_args.argp);
                    base_mat = mat4_mul(mat3_to_mat4(orbit_rot), base_mat);
                    base_mat = mat4_mul(translation_mat4(e_pos), base_mat);
                    base_mat = mat4_mul(mvp, base_mat);

                    if (apsides_a > 0) {

                        let mat0 = scale_mat4(6000 * zoom_scale);
                        mat0 = mat4_mul(translation_mat4([moon_orbit_args.a * (1 - moon_orbit_args.e), 0, 0]), mat0);
                        mat0 = mat4_mul(base_mat, mat0);

                        let mat1 = scale_mat4(6000 * zoom_scale);
                        mat1 = mat4_mul(translation_mat4([moon_orbit_args.a * -(1 + moon_orbit_args.e), 0, 0]), mat1);
                        mat1 = mat4_mul(base_mat, mat1);


                        gl.draw_simple("sphere", mat0, ident_mat3, { color: rgba_hex_color(color3h, apsides_a) });
                        gl.draw_simple("sphere", mat1, ident_mat3, { color: rgba_hex_color(color1h, apsides_a) });

                    }

                    gl.set_blend_enabled(true);
                    gl.set_depth_write_enabled(false);


                    if (m_orbital_ellipse_a > 0) {
                        let apsides_color = rgba_hex_color(color0h, m_orbital_ellipse_a * 0.3);

                        let x1 = -moon_orbit_args.a * moon_orbit_args.e;
                        let x0 = x1 - moon_orbit_args.a;
                        let x2 = x1 + moon_orbit_args.a;

                        gl.draw_ellipse(base_mat, r, [0.1, 0.1, 0.1, 0.1], moon_orbit_args.a, moon_orbit_args.e, 1200 * zoom_scale, undefined, true);
                        gl.draw_segment(base_mat, r, apsides_color, [x0, 0, 0], [x2, 0, 0], 1200 * zoom_scale);

                        let mat0 = scale_mat4(3000 * zoom_scale);
                        mat0 = mat4_mul(translation_mat4([x1, 0, 0]), mat0);
                        mat0 = mat4_mul(base_mat, mat0);

                        gl.draw_simple("sphere", mat0, ident_mat3, { color: [0.4, 0.4, 0.4, 1.0] });


                    }
                } else {
                    gl.set_blend_enabled(true);
                    gl.set_depth_write_enabled(false);

                }

                if (draw_sun) {

                    let mat = mat4_mul(mvp, scale_mat4(sun_radius * planet_sc * 1.4));

                    gl.set_blend_mode("plusl");
                    gl.draw_simple("sun", mat, r, { color: [1, 1, 0.9, 1.0] });
                    gl.set_blend_mode("sover");
                }


                let orbit_mat;
                {
                    orbit_mat = scale_mat4(420000);
                    orbit_mat = mat4_mul(mat3_to_mat4(orbit_rot), orbit_mat);
                    orbit_mat = mat4_mul(translation_mat4(em_orbit_center), orbit_mat);
                    orbit_mat = mat4_mul(mvp, orbit_mat);
                }

                if (orbital_a > 0.0) {
                    let params = {};
                    params.color = rgba_hex_color(0xffffff, orbital_a * 0.1);
                    params.coords = [1, 1, 0, 1];
                    params.feather = 0.99;

                    let quad_mat1 = mat4_mul(orbit_mat, translation_mat4([0, +1, 0.0]));

                    gl.draw_simple("disc", quad_mat1, rot, params);
                }



                if (draw_ecliptic) {


                    let t = 1.0 - zoom_t;
                    let r = lerp(170000000, 106000, smooth_step(0.9, 1.0, 1 - zoom_scale));
                    let pos = vec_lerp([0, 0, 0], emb_pos, smooth_step(0.8, 0.9, t));

                    let mat = scale_mat4(r);
                    mat = mat4_mul(mat3_to_mat4(ecliptic_rot), mat);
                    mat = mat4_mul(translation_mat4(pos), mat);
                    mat = mat4_mul(mvp, mat);


                    let params = {};
                    params.color = rgba_hex_color(0x91B1FF, 0.14);
                    params.feather = 0.99;
                    gl.draw_simple("disc", mat, rot, params);

                    gl.draw_ellipse(mat, rot, vec_scale(params.color, 0.4), 0.995, 0, mid_r / r);


                    if (orbital_a > 0) {
                        let line_of_nodes_p0 = vec_add(emb_pos, vec_scale(line_of_nodes_dir, +420000));
                        let line_of_nodes_p1 = vec_add(emb_pos, vec_scale(line_of_nodes_dir, -420000));

                        gl.draw_segment(mvp, ecliptic_rot, [0.05, 0.05, 0.05, 0.05], line_of_nodes_p0, line_of_nodes_p1, mid_r);
                    }
                }


                if (orbital_a > 0.0) {


                    let params = {};
                    params.color = rgba_hex_color(0xffffff, orbital_a * 0.1);
                    params.coords = [1, 1, 0, 1];
                    params.feather = 0.99;

                    let quad_mat2 = mat4_mul(orbit_mat, translation_mat4([0, -1, 0.0]));

                    params.coords = [1, 1, 0, -1];

                    gl.draw_simple("disc", quad_mat2, rot, params);

                    gl.draw_ellipse(orbit_mat, rot, vec_scale(params.color, 0.4), 0.995, 0, thin_r / 420000);
                }



                if (e_axis_a > 0) {
                    let color = vec_scale([1, 1, 1, 1], e_axis_a * 0.25);
                    let size = 100 * planet_sc;
                    let length = earth_radius * 1.3 * planet_sc;

                    if (big_e_axis) {
                        size = 600000 * zoom_scale;
                        length = 100000000 * zoom_scale;
                        color = rgba_hex_color(color_earth_h, 0.8);
                    }

                    let e_ap0 = [0, 0, earth_radius * 1.05 * planet_sc];
                    let e_ap1 = [0, 0, length];

                    gl.draw_segment(earth_mat, rot, color, e_ap0, e_ap1, size);

                    e_ap0 = [0, 0, -earth_radius * 1.05 * planet_sc];
                    e_ap1 = [0, 0, - length];

                    gl.draw_segment(earth_mat, rot, color, e_ap0, e_ap1, size);
                }

                if (m_axis_a > 0) {
                    let color = vec_scale([1, 1, 1, 1], m_axis_a * 0.25);
                    let size = 40 * planet_sc;
                    let length = moon_radius * 1.3 * planet_sc;

                    if (big_m_axis) {
                        size = 600000 * zoom_scale;
                        length = 100000000 * zoom_scale;
                        color = rgba_hex_color(color_moon_h, 0.8);
                    }

                    let e_ap0 = [0, 0, moon_radius * 1.05 * planet_sc];
                    let e_ap1 = [0, 0, length];

                    gl.draw_segment(moon_mat, rot, color, e_ap0, e_ap1, size);

                    e_ap0 = [0, 0, -moon_radius * 1.05 * planet_sc];
                    e_ap1 = [0, 0, -length];

                    gl.draw_segment(moon_mat, rot, color, e_ap0, e_ap1, size);
                }




                if (emb_alpha > 0.0) {
                    gl.set_depth_test_enabled(false);
                    gl.set_cull_face_enabled(true);
                    let mat = scale_mat4(emb_size);
                    mat = mat4_mul(translation_mat4(emb_pos), mat);
                    mat = mat4_mul(mvp, mat);
                    gl.draw_simple("sphere", mat, ident_mat3, { color: vec_scale([1, 1, 1, 1.0], emb_alpha) });
                    gl.draw_simple("sphere", mat4_mul(mat, scale_mat4(0.7)), ident_mat3, { color: [0, 0, 0, 1] });
                    gl.draw_simple("sphere", mat4_mul(mat, scale_mat4(0.4)), ident_mat3, { color: [1, 1, 1, 1] });
                    gl.set_depth_test_enabled(true);
                    gl.set_cull_face_enabled(false);
                }

                if (emb_x_axis_a > 0.0) {

                    let plane_x = vec_norm(vec_cross([0, 1, 0], orbit_p_z));

                    let dir = vec_scale(plane_x, 430000);

                    let p0 = vec_add(e_pos, vec_scale(plane_x, 1000));
                    let p1 = vec_add(e_pos, dir);
                    gl.draw_segment(mvp, rot, rgba_hex_color(color2h, emb_x_axis_a * 0.3), p0, p1, 1300 * zoom_scale);

                    if (mode === "m_orbit4") {
                        let p0 = vec_add(m_pos, vec_scale(plane_x, 1000));
                        let p1 = vec_add(m_pos, vec_scale(dir, 0.2));
                        gl.draw_segment(mvp, rot, rgba_hex_color(color2h, emb_x_axis_a * 0.3), p0, p1, 1300 * zoom_scale);
                    }
                }


                if (draw_to_sun_dir) {

                    let l = 1;

                    let a = 0.2;
                    let w = 500000 * zoom_scale;

                    {

                        let p0 = e_pos;
                        let p1 = vec_add(e_pos, vec_scale(e_pos, -l));
                        gl.draw_segment(mvp, rot, rgba_hex_color(color0h, a), p0, p1, 500000 * zoom_scale);
                    }

                    {
                        let p0 = m_pos;
                        let p1 = vec_add(m_pos, vec_scale(m_pos, -l));
                        gl.draw_segment(mvp, rot, rgba_hex_color(color0h, a), p0, p1, w);
                    }
                }

                if (draw_to_reference_dir) {

                    let l = 150000000;
                    let p0 = e_pos;
                    let p1 = vec_add(e_pos, [l, 0, 0]);
                    gl.draw_segment(mvp, rot, rgba_hex_color(color2h, 0.3), p0, p1, 500000 * zoom_scale);

                    {
                        let p0 = m_pos;
                        let p1 = vec_add(m_pos, [l, 0, 0]);
                        gl.draw_segment(mvp, rot, rgba_hex_color(color2h, 0.3), p0, p1, 500000 * zoom_scale);
                    }
                }


                if (ecliptic_x_axis_a > 0.0) {

                    let plane_x = vec_norm(vec_cross([0, 1, 0], ecliptic_p_z));

                    let dir = vec_scale(plane_x, 430000);

                    let p0 = emb_pos
                    let p1 = vec_add(emb_pos, dir);
                    gl.draw_segment(mvp, rot, rgba_hex_color(color2h, ecliptic_x_axis_a * 0.3), p0, p1, thick_r);
                }


                if (draw_line_of_nodes) {
                    let line_of_nodes_p0 = vec_add(emb_pos, vec_scale(line_of_nodes_dir, +line_of_nodes_length));
                    let line_of_nodes_p1 = vec_add(emb_pos, vec_scale(line_of_nodes_dir, -line_of_nodes_length));

                    gl.draw_segment(mvp, rot, rgba_hex_color(0xE4A26D, 0.3), line_of_nodes_p0, line_of_nodes_p1, thick_r * 0.8);
                }


                if (inclination_a > 0) {

                    let dir0 = vec_cross(line_of_nodes_dir, ecliptic_p_z);
                    let dir1 = vec_cross(line_of_nodes_dir, orbit_p_z);
                    let inclination = acos(vec_dot(dir0, dir1));

                    let plane_z = line_of_nodes_dir;
                    let plane_x = dir0;
                    let plane_y = vec_cross(plane_z, plane_x);


                    let plane_mat = [
                        plane_x[0], plane_x[1], plane_x[2],
                        plane_y[0], plane_y[1], plane_y[2],
                        plane_z[0], plane_z[1], plane_z[2]];

                    plane_mat = mat3_transpose(plane_mat);

                    let mat = mat3_to_mat4(plane_mat);
                    mat = mat4_mul(translation_mat4(emb_pos), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_segment(mvp, rot, [0.1, 0.1, 0.1, 0.1], emb_pos, vec_add(emb_pos, vec_scale(dir0, 430000)), mid_r);
                    gl.draw_segment(mvp, rot, [0.1, 0.1, 0.1, 0.1], emb_pos, vec_add(emb_pos, vec_scale(dir1, 430000)), mid_r);


                    gl.draw_ellipse(mat, r, rgba_hex_color(color3h, inclination_a), 300000, 0, thick_r, -inclination);
                }

                if (line_of_nodes_angle_a > 0) {

                    let plane_z = ecliptic_p_z;
                    let plane_x = vec_norm(vec_cross([0, 1, 0], plane_z));
                    let plane_y = vec_cross(plane_x, plane_z);

                    let plane_mat = [
                        plane_x[0], plane_x[1], plane_x[2],
                        plane_y[0], plane_y[1], plane_y[2],
                        plane_z[0], plane_z[1], plane_z[2]];

                    let mat = mat3_to_mat4(plane_mat);
                    mat = mat4_mul(translation_mat4(emb_pos), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_ellipse(mat, r, rgba_hex_color(color0h, line_of_nodes_angle_a * 0.3), 380000, 0, thick_r, -omega);
                }

                let e_axis_angle;
                let m_axis_angle;

                if (mode === "em_orbit8" || mode === "em_orbit9") {

                    {
                        let axis = mat3_mul_vec(earth_rot, [0, 0, 1]);

                        let plane_z = vec_norm(vec_cross(axis, ecliptic_p_z));
                        let plane_x = ecliptic_p_z;
                        let plane_y = vec_cross(plane_x, plane_z);


                        let plane_mat = [
                            plane_x[0], plane_x[1], plane_x[2],
                            plane_y[0], plane_y[1], plane_y[2],
                            plane_z[0], plane_z[1], plane_z[2]];

                        plane_mat = mat3_transpose(plane_mat);

                        let w = 50000000 * zoom_scale;
                        let h = 100000000 * zoom_scale;


                        {
                            let mat = mat3_to_mat4(plane_mat);
                            mat = mat4_mul(translation_mat4(e_pos), mat);
                            mat = mat4_mul(mvp, mat);

                            if (mode != "em_orbit9")
                                gl.draw_ellipse(mat, r, rgba_hex_color(color0h), 100000000 * zoom_scale * 0.9, 0, thick_r, e_inclination_angle);

                            gl.draw_segment(mvp, rot, [0.1, 0.1, 0.1, 0.1], e_pos, vec_add(e_pos, vec_scale(ecliptic_p_z, 100000000 * zoom_scale)), mid_r);
                        }
                        if (mode === "em_orbit9") {


                            let aplane_z = ecliptic_p_z;
                            let aplane_x = vec_cross([1, 0, 0], aplane_z);
                            let aplane_y = vec_cross(aplane_z, aplane_x);


                            let plane_mat = [
                                aplane_y[0], aplane_y[1], aplane_y[2],
                                aplane_x[0], aplane_x[1], aplane_x[2],
                                aplane_z[0], aplane_z[1], aplane_z[2],
                            ];
                            plane_mat = mat3_transpose(plane_mat);



                            let mat = mat3_to_mat4(plane_mat);
                            mat = mat4_mul(translation_mat4(e_pos), mat);
                            mat = mat4_mul(mvp, mat);

                            let a = acos(vec_dot(plane_y, [1, 0, 0]));

                            if (vec_dot(vec_cross(plane_y, [1, 0, 0]), ecliptic_p_z) > 0)
                                a = 2 * pi - a;

                            e_axis_angle = a;

                            gl.draw_ellipse(mat, r, rgba_hex_color(color4h), 50000000 * zoom_scale * 0.9, 0, thick_r, -a);

                            gl.draw_segment(mvp, rot, [0.1, 0.1, 0.1, 0.1], e_pos, vec_add(e_pos, vec_scale(plane_y, 80000000 * zoom_scale)), mid_r);

                            gl.draw_segment(mvp, rot, rgba_hex_color(color2h, 0.3), e_pos, vec_add(e_pos, vec_scale([1, 0, 0], 80000000 * zoom_scale)), mid_r);
                        }



                        let c = rgba_hex_color(color_earth_h, 0.25)

                        gl.draw_segment(mvp, rot, c,
                            vec_add(e_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, h))),
                            vec_add(e_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, -h))),
                            thin_r);

                        gl.draw_segment(mvp, rot, c,
                            vec_add(e_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, h))),
                            vec_add(e_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, -h))),
                            thin_r);

                        gl.draw_segment(mvp, rot, c,
                            vec_add(e_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, -h))),
                            vec_add(e_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, -h))),
                            thin_r);

                        gl.draw_segment(mvp, rot, c,
                            vec_add(e_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, h))),
                            vec_add(e_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, h))),
                            thin_r);
                    }

                    {
                        let axis = mat3_mul_vec(moon_rot, [0, 0, 1]);

                        let plane_z = vec_norm(vec_cross(axis, ecliptic_p_z));
                        let plane_x = ecliptic_p_z;
                        let plane_y = vec_cross(plane_x, plane_z);


                        let plane_mat = [
                            plane_x[0], plane_x[1], plane_x[2],
                            plane_y[0], plane_y[1], plane_y[2],
                            plane_z[0], plane_z[1], plane_z[2]];

                        plane_mat = mat3_transpose(plane_mat);

                        let mat = mat3_to_mat4(plane_mat);
                        mat = mat4_mul(translation_mat4(m_pos), mat);
                        mat = mat4_mul(mvp, mat);

                        {

                            if (mode != "em_orbit9")
                                gl.draw_ellipse(mat, r, rgba_hex_color(color1h), 100000000 * zoom_scale * 0.9, 0, thick_r, m_inclination_angle);

                            gl.draw_segment(mvp, rot, [0.1, 0.1, 0.1, 0.1], m_pos, vec_add(m_pos, vec_scale(ecliptic_p_z, 100000000 * zoom_scale)), mid_r);
                        }
                        if (mode === "em_orbit9") {


                            let aplane_z = ecliptic_p_z;
                            let aplane_x = vec_cross([1, 0, 0], aplane_z);
                            let aplane_y = vec_cross(aplane_z, aplane_x);


                            let plane_mat = [
                                aplane_y[0], aplane_y[1], aplane_y[2],
                                aplane_x[0], aplane_x[1], aplane_x[2],
                                aplane_z[0], aplane_z[1], aplane_z[2],
                            ];
                            plane_mat = mat3_transpose(plane_mat);


                            let mat = mat3_to_mat4(plane_mat);
                            mat = mat4_mul(translation_mat4(m_pos), mat);
                            mat = mat4_mul(mvp, mat);

                            let a = acos(vec_dot(plane_y, [1, 0, 0]));

                            if (vec_dot(vec_cross(plane_y, [1, 0, 0]), ecliptic_p_z) > 0)
                                a = 2 * pi - a;


                            m_axis_angle = a;
                            gl.draw_ellipse(mat, r, rgba_hex_color(color5h), 60000000 * zoom_scale * 0.9, 0, thick_r, -a);

                            gl.draw_segment(mvp, rot, [0.1, 0.1, 0.1, 0.1], m_pos, vec_add(m_pos, vec_scale(plane_y, 100000000 * zoom_scale)), mid_r);

                            gl.draw_segment(mvp, rot, rgba_hex_color(color2h, 0.3), m_pos, vec_add(m_pos, vec_scale([1, 0, 0], 100000000 * zoom_scale)), mid_r);

                        }


                        let w = 50000000 * zoom_scale;
                        let h = 100000000 * zoom_scale;

                        let c = rgba_hex_color(color_moon_h, 0.15)


                        gl.draw_segment(mvp, rot, c,
                            vec_add(m_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, h))),
                            vec_add(m_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, -h))),
                            thin_r);

                        gl.draw_segment(mvp, rot, c,
                            vec_add(m_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, h))),
                            vec_add(m_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, -h))),
                            thin_r);

                        gl.draw_segment(mvp, rot, c,
                            vec_add(m_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, -h))),
                            vec_add(m_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, -h))),
                            thin_r);

                        gl.draw_segment(mvp, rot, c,
                            vec_add(m_pos, vec_add(vec_scale(plane_y, w), vec_scale(plane_x, h))),
                            vec_add(m_pos, vec_add(vec_scale(plane_y, -w), vec_scale(plane_x, h))),
                            thin_r);
                    }


                }



                if (m_cone_a) {

                    let local_observer_pos = [0, 0, earth_radius];
                    let observer_pos = vec_add(e_pos, mat3_mul_vec(earth_rot, local_observer_pos));


                    {
                        let mat0 = scale_mat4(100);
                        mat0 = mat4_mul(translation_mat4(observer_pos), mat0);
                        mat0 = mat4_mul(mvp, mat0);

                        gl.draw_simple("sphere", mat0, ident_mat3, { color: rgba_hex_color(0xff0000, 1) });
                    }


                    {
                        let dir = vec_sub(m_pos, observer_pos);
                        let l = vec_len(dir);
                        let c = moon_radius * planet_sc / l;
                        let s = sqrt(1 - c * c);
                        let r = moon_radius * s * planet_sc;
                        let h = l - c * r;

                        let z = vec_scale(dir, 1 / l);
                        let x = vec_norm(vec_cross(ecliptic_p_z, z));
                        let y = vec_cross(z, x);


                        let ra = [
                            x[0], x[1], x[2],
                            y[0], y[1], y[2],
                            z[0], z[1], z[2],
                        ];

                        ra = mat3_transpose(ra);

                        let mat0 = scale_mat4([r, r, h]);
                        mat0 = mat4_mul(mat3_to_mat4(ra), mat0);
                        mat0 = mat4_mul(translation_mat4(observer_pos), mat0);
                        mat0 = mat4_mul(mvp, mat0);

                        gl.draw_simple("cone", mat0, ident_mat3, { color: [0.2, 0.2, 0.2, 0.2] });
                    }


                }

                if (mode === "em_orbit30") {

                    let base_rot = mat3_transpose(r);

                    function draw_cones(pos, r) {
                        r *= planet_sc;
                        let R = sun_radius * planet_sc;
                        let l = vec_len(pos);
                        let Rr = R - r;

                        let L0 = l * R / Rr;
                        let L1 = l * Rr / R;

                        let d0 = L0 - l;
                        let b0 = sqrt(d0 * d0 - r * r);

                        let d1 = l - L1;
                        let b1 = sqrt(d1 * d1 - r * r);


                        let s0 = r / d0;
                        let c0 = sqrt(1 - s0 * s0);

                        let s1 = r / d1;
                        let c1 = sqrt(1 - s1 * s1);

                        let r0 = r * c0;
                        let h0 = b0 * c0;
                        let pos0 = vec_scale(pos, L0 / l);

                        let r1 = r * c1;
                        let h1 = b1 * c1;
                        let pos1 = vec_scale(pos, L1 / l);


                        let z = vec_scale(pos, 1 / l);
                        let x = vec_norm(vec_cross(mat3_mul_vec(base_rot, [0, 0, 1]), z));
                        let y = vec_cross(z, x);

                        let ra = [
                            x[0], x[1], x[2],
                            y[0], y[1], y[2],
                            z[0], z[1], z[2],
                        ];


                        ra = mat3_transpose(ra);

                        let rr = mat3_mul(base_rot, ra);

                        let mat0 = scale_mat4([r0, r0, -h0]);
                        mat0 = mat4_mul(mat3_to_mat4(ra), mat0);
                        mat0 = mat4_mul(translation_mat4(pos0), mat0);
                        mat0 = mat4_mul(mvp, mat0);





                        let sc = 120.0;
                        let mat1 = scale_mat4(vec_scale([r1, r1, h1], sc));
                        mat1 = mat4_mul(mat3_to_mat4(ra), mat1);
                        mat1 = mat4_mul(translation_mat4(pos1), mat1);
                        mat1 = mat4_mul(mvp, mat1);

                        gl.draw_simple("shadow_cone", mat1, rr, {
                            color: [0.0, 0.0, 0., 0.1],
                            params: [-1 / sc, -1.0, 0, 0],
                            norm_z: r1 / h1,
                        });


                        gl.draw_simple("shadow_cone", mat0, rr, {
                            color: [0.0, 0.0, 0., 0.2],
                            params: [0, -1.0, 0, 0],
                            norm_z: r0 / h0,
                        });


                    }

                    draw_cones(m_pos, moon_radius);
                    draw_cones(e_pos, earth_radius);
                }


                {
                    gl.update_trail_buffer(state.hist);

                    let alpha_range = [0, trail_alpha_range, history_count - 1, history_count - 1];

                    if (draw_emb_trail)
                        gl.draw_trail(mvp, rot, 0, history_count, { color: [0.3, 0.3, 0.3, 0.3], offset: trail_reference, alpha_range });

                    if (draw_e_trail)
                        gl.draw_trail(mvp, rot, history_count * 3, history_count, { color: rgba_hex_color(0x386391, 0.5), offset: trail_reference, alpha_range });

                    if (draw_m_trail)
                        gl.draw_trail(mvp, rot, history_count * 6, history_count, { color: vec_scale([1, 1, 1, 1], m_trail_a), offset: trail_reference, alpha_range });
                }



                if (sunlight) {

                    let mat = scale_mat4(6471 * planet_sc);

                    gl.set_cull_face_enabled(true);

                    let view_dir = mat3_mul_vec(mat3_transpose(mat3_mul(r, earth_rot)), [0, 0, 1]);
                    let dir = mat3_mul_vec(mat3_transpose(earth_rot), vec_neg(vec_norm(e_pos)));


                    gl.set_blend_mode("plusl");
                    gl.draw_simple("earth_sky", mat4_mul(earth_mat, mat), rot, {
                        light_dir: dir,
                        view_dir: view_dir,
                    });
                    gl.set_blend_mode("sover");

                }


                if (mode === "em_orbit30") {
                    gl.set_blend_mode("dover");
                    gl.draw_full("color_fill", { color: [0.15, 0.15, 0.15, 0.15] });
                    gl.set_blend_mode("sover");
                }

                ctx.drawImage(gl.finish(), 0, 0, w, h);

                if (state.anomalistic_markers) {

                    ctx.save();
                    ctx.translate(width / 2, width / 2);

                    ctx.font = ceil(font_size * 0.7) + "px IBM Plex Sans";

                    let i = 1;
                    for (let marker of state.anomalistic_markers) {

                        ctx.globalAlpha = smooth_step(0, anomalistic_markers_count / 4, anomalistic_markers_count - state.anomalistic_markers.length + i);

                        let p = project(mat4_mul_vec3(mvp, vec_add(e_pos, marker)));

                        p[0] *= 1.1;
                        p[1] *= 1.1;

                        let str = state.anomalistic_markers_i + i;
                        let w = ctx.measureText(str).width;

                        ctx.fillStyle = "rgba(20, 20, 20, 0.8)";
                        ctx.roundRect(p[0] - w, p[1] - font_size * 0.7, 2 * w, font_size, font_size * 0.2);
                        ctx.fill();
                        ctx.fillStyle = "rgba(255, 255, 255, 0.4)";
                        ctx.fillText(str, p[0], p[1]);

                        i++;
                    }
                    ctx.restore();
                }



                let feather_size = canvas.height * 0.05 * feather_scale;

                ctx.feather(width * scale, height * scale,
                    feather_size, feather_size, feather_size, feather_size);

                let strings = [];
                let colors = ["#aaa", "#aaa"];

                if (mode === "m_orbit2") {
                    strings[0] = `eccentricity = ${moon_orbit_args.e.toFixed(4)}`;
                    strings[1] = `semi-major axis = ${pretty_distance(moon_orbit_args.a)}`;
                } else if (mode === "em_orbit5") {
                    let dir0 = vec_cross(line_of_nodes_dir, ecliptic_p_z);
                    let dir1 = vec_cross(line_of_nodes_dir, orbit_p_z);
                    let inclination = acos(vec_dot(dir0, dir1));

                    strings[0] = `inclination = ${pretty_angle(inclination)}`;
                    colors[0] = color3;
                } else if (mode === "em_orbit7" || mode === "em_orbit7a") {
                    strings[0] = `longitude of the ascending node = ${pretty_angle(omega)}`;
                    colors[0] = color0;
                } else if (mode === "em_orbit8") {
                    strings[0] = `Earth's axial tilt = ${pretty_angle(ecliptic_inclination + eph.earth_axial_tilt(t))}`;
                    strings[1] = `Moon's axial tilt = ${pretty_angle(m_inclination_angle)}`;
                    colors[0] = color0;
                    colors[1] = color1;
                }
                else if (mode === "em_orbit9") {
                    strings[0] = `Earth's axis angle = ${pretty_angle(e_axis_angle)}`;
                    strings[1] = `Moon's axis angle = ${pretty_angle(m_axis_angle)}`;
                    colors[0] = color4;
                    colors[1] = color5;
                } else if (mode === "em_orbit12") {
                    strings[0] = `relative angle = ${pretty_angle(orbit_p_z_earth_axis_angle)}`;
                    colors[0] = color0;
                } else if (mode === "em_orbit25") {
                    ctx.save();
                    ctx.fillStyle = "white";

                    ctx.translate(width / 2, height - font_size);
                    draw_moon_phase_label(m_pos, e_pos, ecliptic_p_z);
                    ctx.restore();
                }

                for (let i = 0; i < strings.length; i++) {
                    ctx.fillStyle = colors[i];
                    ctx.fillText(strings[i], width / 2, height - font_size * (strings.length - i * 1.5));
                }

                if (show_date) {
                    draw_date_and_time(width * 0.96, width * 0.04, t, false, mode !== "em_orbit30");
                }

            } else if (mode.startsWith("angular_momentum")) {

                if (!state) {
                    state = {};
                    state.a = 0;
                }

                let r = lerp(1.5, 4.5, slider_args[0]);
                let m = 1;
                let I = 3 * m * r * r;

                let w = 30 / I;

                state.a += w * dt;

                let sr0 = 1;
                let sr1 = 1.2599210499;


                ctx.translate(width / 2, height / 2);

                ctx.rotate(-state.a);

                let s = width / 21;

                ctx.scale(s, s);

                function draw(inset = 0) {
                    ctx.fillRect(-10, -0.15 + inset, 20, 0.3 - 2 * inset);
                    ctx.fillEllipse(-10, 0, 0.15 - inset);
                    ctx.fillEllipse(10, 0, 0.15 - inset);
                    ctx.fillEllipse(0, 0, 0.3 - inset);
                }

                ctx.fillStyle = "#555";
                draw();


                draw_barycenter(0, 0, 0.15);

                ctx.save();
                ctx.shadowColor = "rgba(0,0,0,0.9)";
                ctx.shadowBlur = 10;

                ctx.fillStyle = sphere_gradient(2 * r, 0, sr0, rgba_hex_color(color0h));
                ctx.fillEllipse(2 * r, 0, sr0);

                ctx.fillStyle = sphere_gradient(-r, 0, sr1, rgba_hex_color(color2h));
                ctx.fillEllipse(-r, 0, sr1);
                ctx.restore();


                ctx.lineWidth = 0.07;
                ctx.strokeStyle = "rgba(255,255,255,0.3)";
                ctx.strokeLine(-r, 0, -r, 2);
                ctx.strokeLine(2 * r, 0, 2 * r, 2);

                ctx.lineWidth = 0.1;
                ctx.lineCap = "butt";
                ctx.strokeStyle = color1;
                ctx.strokeLine(-r, 1.8, 2 * r, 1.8);


            } else if (mode.startsWith("twist")) {

                let a = (1.0 - slider_args[0]) * 0.3;

                ctx.translate(width / 2, height / 2);

                ctx.rotate(-a);

                let sc = width / 21;

                ctx.scale(sc, sc);

                function draw(inset = 0) {
                    ctx.fillRect(-5, -0.15 + inset, 10, 0.3 - 2 * inset);
                    ctx.fillEllipse(-5, 0, 0.3 - inset);
                    ctx.fillEllipse(5, 0, 0.3 - inset);
                    ctx.fillEllipse(0, 0, 0.3 - inset);

                }

                ctx.fillStyle = "#555";
                draw();



                ctx.save();

                ctx.shadowOffsetX = ctx.shadowOffsetX = 0;
                ctx.shadowBlur = 10;
                ctx.shadowColor = "rgba(0,0,0,1)";

                ctx.fillStyle = "#000";
                ctx.fillEllipse(5.0, 0, 0.12);
                ctx.fillEllipse(-5.0, 0, 0.12);

                ctx.fillStyle = "#888";
                ctx.strokeStyle = "#333";

                ctx.lineWidth = 0.03;
                ctx.fillEllipse(0, 0, 0.1);
                ctx.strokeEllipse(0, 0, 0.1);

                ctx.restore();

                let c = cos(-a);
                let s = sin(-a);
                let d = 20;

                let p0 = [5.0, 0];
                let p1 = [c * d, -s * d];
                let dir = vec_norm(vec_sub(p1, p0));
                p0 = vec_add(p0, vec_scale(dir, 0.04));

                for (let k = 0; k < 2; k++) {

                    ctx.fillStyle = ctx.strokeStyle = "#60482F";
                    ctx.lineWidth = 0.12;
                    ctx.strokeLine(p0[0], p0[1], p1[0], p1[1]);
                    ctx.fillEllipse(p0[0], p0[1], 0.09);

                    ctx.lineWidth = 0.1;

                    let n = 50;

                    for (let i = 0; i < n; i++) {
                        ctx.strokeStyle = i & 1 ? "#6D543A" : "#57422D";
                        let step = 0.17;
                        let w = i == 0 ? 0.02 : 0.04;
                        let d = i == 0 ? 0.04 : 0.08;



                        ctx.strokeLine(p0[0] + dir[0] * (step * i + d) - dir[1] * w, p0[1] + dir[1] * (step * i + d) + dir[0] * w,
                            p0[0] + dir[0] * (step * i - d) + dir[1] * w, p0[1] + dir[1] * (step * i - d) - dir[0] * w
                        );
                    }


                    ctx.lineWidth = 0.05;


                    ctx.fillStyle = color0;
                    ctx.strokeStyle = "#111";

                    ctx.arrow(p0[0] + dir[0] * 2, p0[1] + dir[1] * 2,
                        p0[0] + dir[0] * 4, p0[1] + dir[1] * 4,
                        0.3, 0.7, 0.9);
                    ctx.fill();
                    ctx.stroke();

                    p0 = vec_neg(p0);
                    p1 = vec_neg(p1);
                    dir = vec_neg(dir);
                }


                ctx.feather(width * scale, height * scale,
                    canvas.height * 0.1, canvas.height * 0.1,
                    canvas.height * 0.1, canvas.height * 0.1);
            } else if (mode === "shadow") {


                if (draggables.length == 0) {
                    draggables = [
                        {
                            pos: [0.35, 0.16], size: 0.03, limiter: ((x) => {
                                x[0] = clamp(x[0], 0.17, 0.55);
                                x[1] = clamp(x[1], 0.03, 0.27);
                                return x;
                            })
                        }]
                }



                let hh = round(height * 0.5);


                let x0 = width * 0.06;
                let x1 = width * draggables[0].pos[0];
                let x2 = width * 0.6;

                let y1 = round(width * draggables[0].pos[1]) - hh;


                let R = width * 0.05;
                let r = width * 0.02;

                let Rr = R - r;

                let l20 = x2 - x0;
                let s20 = R / l20;
                let c20 = sqrt(1 - s20 * s20);

                let l21 = sqrt((x2 - x1) * (x2 - x1) + y1 * y1);
                let s21 = r / l21;
                let c21 = sqrt(1 - s21 * s21);


                let dir1 = vec_norm([x1 - x0, y1]);
                let perp1 = [dir1[1], -dir1[0]];

                let l10 = sqrt((x1 - x0) * (x1 - x0) + y1 * y1);

                let L10 = l10 * R / Rr;

                let s10 = R / L10;
                let c10 = sqrt(1 - s10 * s10);


                let m = l10 * R / (R + r);
                let sm = R / m;
                let cm = sqrt(1 - sm * sm);


                let d0 = vec_scale([dir1[0] * sm + perp1[0] * cm, dir1[1] * sm + perp1[1] * cm], R);
                let d1 = vec_scale([dir1[0] * sm - perp1[0] * cm, dir1[1] * sm - perp1[1] * cm], R);

                let mm = vec_scale(dir1, m);

                let w0 = vec_sub(mm, d0);
                let w1 = vec_sub(mm, d1);


                gl.begin(width, height);

                let ortho_proj = [
                    1 / width, 0, 0, 0,
                    0, 1 / height, 0, 0,
                    0, 0, -0.005, 0,
                    0, 0, 0, 1
                ];
                {
                    let mat = scale_mat4(2.0 * r * 1.01);
                    mat = mat4_mul(translation_mat4([2 * x1 - width, -2 * y1 + height - hh * 2, 0]), mat);
                    mat = mat4_mul(ortho_proj, mat);

                    gl.draw_simple("proto", mat, ident_mat3, { color: rgba_hex_color(color2h) });

                }

                {
                    let mat = scale_mat4(height * 0.745);
                    mat = mat4_mul(translation_mat4([width - hh * 2, 0, 0]), mat);
                    mat = mat4_mul(ortho_proj, mat);

                    gl.draw_simple("sun_eclipse", mat, ident_mat3, {
                        color: rgba_hex_color(color4h),
                        dim: 1,
                        dir0: [0, 0, 0, 0],
                        dir1: [0, 0, 0, 0],
                        dir2: [0, 0, 0, 0],
                    });

                }


                ctx.save();
                ctx.translate(0, hh);

                ctx.beginPath();

                ctx.lineTo(x0 + d1[0] + w1[0] * (R + r) / R, d1[1] + w1[1] * (R + r) / R);
                ctx.lineTo(x0 + d1[0] + w1[0] * (R + r) / R * 10, d1[1] + w1[1] * (R + r) / R * 10);
                ctx.lineTo(x0 + d0[0] + w0[0] * (R + r) / R * 10, d0[1] + w0[1] * (R + r) / R * 10);
                ctx.lineTo(x0 + d0[0] + w0[0] * (R + r) / R, d0[1] + w0[1] * (R + r) / R);


                ctx.globalCompositeOperation = "source-over";

                ctx.fillStyle = rgba_color_string(rgba_hex_color(color1h, 0.5));
                ctx.strokeStyle = rgba_color_string(rgba_hex_color(color1h, 0.9));

                ctx.fill();
                ctx.stroke();




                ctx.beginPath();

                ctx.lineTo(x0 + dir1[0] * L10, dir1[1] * L10);
                ctx.lineTo(x1 + r * (dir1[0] * s10 + perp1[0] * c10), y1 + r * (dir1[1] * s10 + perp1[1] * c10));
                ctx.lineTo(x1 + r * (dir1[0] * s10 - perp1[0] * c10), y1 + r * (dir1[1] * s10 - perp1[1] * c10));
                ctx.closePath();



                ctx.fillStyle = "#000";

                ctx.globalCompositeOperation = "destination-out";
                ctx.fill();

                ctx.globalCompositeOperation = "source-over";

                ctx.fillStyle = rgba_color_string(rgba_hex_color(color3h, 0.5));
                ctx.strokeStyle = rgba_color_string(rgba_hex_color(color3h, 0.9));

                ctx.fill();
                ctx.stroke();



                ctx.strokeStyle = "#333";
                ctx.setLineDash([width * 0.003, width * 0.006]);
                ctx.lineWidth = 1;

                ctx.strokeStyle = rgba_color_string(rgba_hex_color(color3h, 0.7));

                ctx.strokeLine(

                    x0 + R * (dir1[0] * s10 - perp1[0] * c10),
                    R * (dir1[1] * s10 - perp1[1] * c10),
                    x1 + r * (dir1[0] * s10 - perp1[0] * c10),
                    y1 + r * (dir1[1] * s10 - perp1[1] * c10)
                );


                ctx.strokeLine(
                    x0 + R * (dir1[0] * s10 + perp1[0] * c10),
                    R * (dir1[1] * s10 + perp1[1] * c10),
                    x1 + r * (dir1[0] * s10 + perp1[0] * c10),
                    y1 + r * (dir1[1] * s10 + perp1[1] * c10)

                );

                ctx.strokeStyle = rgba_color_string(rgba_hex_color(color1h, 0.7));

                ctx.strokeLine(
                    x0 + d0[0],
                    d0[1],
                    x0 + d0[0] + w0[0] * (R + r) / R,
                    d0[1] + w0[1] * (R + r) / R,
                );


                ctx.strokeLine(
                    x0 + d1[0],
                    d1[1],
                    x0 + d1[0] + w1[0] * (R + r) / R,
                    d1[1] + w1[1] * (R + r) / R,
                );


                ctx.strokeStyle = "rgba(255, 255, 255, 0.2)";

                ctx.strokeLine(x0 + R * s20, R * c20, x2, 0);
                ctx.strokeLine(x0 + R * s20, -R * c20, x2, 0);


                ctx.setLineDash([]);

                ctx.fillStyle = "white";

                ctx.save();
                ctx.shadowColor = "rgba(255,255,255,1)";
                ctx.shadowBlur = width * 0.03;
                ctx.shadowOffsetY = 0;
                ctx.shadowOffsetX = 0;
                ctx.fillEllipse(x0, 0, R);
                ctx.restore();


                ctx.globalCompositeOperation = "destination-out";
                ctx.fillEllipse(x1, y1, r);
                ctx.globalCompositeOperation = "source-over";

                ctx.fillStyle = "#f64c4c";
                ctx.fillEllipse(x2, 0, width * 0.004);

                ctx.translate(width - hh, 0);
                ctx.beginPath();

                ctx.rect(-hh, -height, height * 2, height * 2);
                ctx.fillStyle = "black";
                ctx.globalCompositeOperation = "destination-out";
                ctx.fill();
                ctx.globalCompositeOperation = "source-over";

                ctx.save();
                ctx.clip();

                let sc = height * 4;

                let rr0 = sc * acos(c20);
                let rr1 = sc * acos(c21)


                let y = sc * atan2(y1, x2 - x1);


                ctx.fillStyle = "black";
                ctx.fillEllipse(0, y, rr1);

                let n = 90;
                let w = rr0 * 2 * pi / n;

                ctx.setLineDash([w, w]);
                ctx.lineWidth = 1.5;
                ctx.strokeStyle = "rgba(255,255,255,0.2)";
                ctx.globalCompositeOperation = "source-atop";
                ctx.strokeEllipse(0, 0, rr0);

                ctx.restore();

                ctx.restore();

                ctx.globalCompositeOperation = "destination-over";

                ctx.drawImage(gl.finish(), 0, 0, width, height);
                ctx.globalCompositeOperation = "source-over";


                ctx.feather((width - height) * scale, height * scale,
                    0, canvas.height * 0.1,
                    canvas.height * 0.1, canvas.height * 0.1);

                ctx.setLineDash([]);
                ctx.strokeStyle = "#222";
                ctx.strokeLine(width - height, 0, width - height, height);





            } else if (mode.startsWith("ellipse")) {

                if (!state) {
                    state = {};
                    state.a = 0;
                }


                let a = 1.0;
                let ecc = 0.5;
                let slide = slider_args[0];

                if (mode === "ellipse1") {
                    a = lerp(0.6, 1.0, slider_args[0]);
                    ecc = lerp(0.0, 0.7, slider_args[1]);
                    slide = 0;
                }
                let c0 = color0;
                let c2 = color2;

                let c0hex = rgba_hex_color(color0h);
                let c2hex = rgba_hex_color(color2h);
                if (mode === "ellipse3") {
                    let dim = rgba_hex_color(0x777777);
                    c0hex = vec_lerp(rgba_hex_color(color0h), dim, 0.6);
                    c0 = rgba_color_string(c0hex);
                    c2hex = vec_lerp(rgba_hex_color(color2h), dim, 0.6);
                    c2 = rgba_color_string(c2hex);
                }


                let b = a * Math.sqrt(1 - ecc * ecc);
                let c = ecc * a;

                let T_scale = 2.1;

                let T = 2 * pi * sqrt(a * a * a);
                T *= T_scale;



                state.a += -dt * 2 * pi / T;

                let r0 = 0.03 * 2;
                let r1 = 0.043 * 2;


                let ecc_a = eccentric_anomaly(ecc, state.a);
                let angle = true_anomaly(ecc, ecc_a);

                let r = a * (1 - ecc * ecc) / (1 + ecc * cos(angle));

                let p0 = [c + r * cos(angle), r * sin(angle)];
                let p1 = [c, 0];

                let pb = vec_lerp(p0, p1, 0.75);



                ctx.translate(width / 2, height / 2);

                if (mode === "ellipse3") {
                    ctx.translate(0, -width * 0.1);
                }

                ctx.save();

                let center = [0, 0];

                let s = width * 0.3;

                ctx.lineWidth = 2;
                ctx.globalAlpha = 0.5;
                if (mode === "ellipse1") {
                    ctx.translate(0, width * 0.05);

                    s = width * 0.4;
                    ctx.strokeStyle = "#888";

                    ctx.beginPath();
                    ctx.ellipse(0, 0, a * s * (1 - slide), b * s * (1 - slide), 0, 0, 2 * Math.PI);
                    ctx.stroke();

                } else {
                    ctx.strokeStyle = c0;
                    ctx.globalAlpha = 0.4;
                    ctx.lineCap = "butt";

                    center = vec_lerp(p1, p0, slide);

                    ctx.translate(-center[0] * s, -center[1] * s);



                    let N = 40;
                    let n = 4;

                    let x = -(p1[0] - center[0]) * s + c * s;
                    let y = -(p1[1] - center[1] * s)

                    ctx.beginPath();

                    ctx.ellipse(-(p1[0] - center[0]) * s + c * slide * s, -(p1[1] - center[1] * s), a * s * (1 - slide), b * s * (1 - slide), 0, 0, 2 * Math.PI);
                    ctx.stroke();

                    ctx.globalAlpha = 0.6;

                    for (let i = 0; i < N; i++) {
                        ctx.beginPath();
                        for (let j = 0; j <= n; j++) {
                            let t = i / N + j * 0.5 / n / N;
                            let ta = t * 2 * pi;

                            let ecc_a = eccentric_anomaly(ecc, ta);
                            let angle = true_anomaly(ecc, ecc_a);
                            let r = a * (1 - ecc * ecc) / (1 + ecc * cos(angle)) * s * (1 - slide);

                            ctx.lineTo(x + r * cos(angle), y + r * sin(angle));
                        }
                        ctx.stroke();
                    }


                    ctx.strokeStyle = c2;


                    ctx.globalAlpha = 0.4;

                    if (slide > 0) {
                        ctx.beginPath();

                        ctx.ellipse(-(p1[0] - center[0]) * s + c * s + c * s * slide,
                            -(p1[1] - center[1]) * s,
                            a * s * slide, b * s * slide, 0, 0, 2 * Math.PI);
                        ctx.stroke();
                    }

                    ctx.globalAlpha = 0.6;


                    for (let i = 0; i < N; i++) {
                        ctx.beginPath();
                        for (let j = 0; j <= n; j++) {
                            let t = i / N + j * 0.5 / n / N;
                            let ta = t * 2 * pi;

                            let ecc_a = eccentric_anomaly(ecc, ta);
                            let angle = true_anomaly(ecc, ecc_a);
                            let r = a * (1 - ecc * ecc) / (1 + ecc * cos(angle)) * s * slide;

                            ctx.lineTo(x - r * cos(angle), y - r * sin(angle));
                        }
                        ctx.stroke();
                    }


                }


                ctx.globalAlpha = 1;


                if (mode === "ellipse1") {

                    {
                        ctx.fillStyle = color2;

                        let estr0 = "eccentricity"
                        let eqstr = " = ";
                        let estr1 = ecc.toFixed(2);
                        let gap = font_size * 2;

                        let w0 = ctx.measureText(estr0).width;
                        let we = ctx.measureText(eqstr).width;
                        let w1 = ctx.measureText(estr1).width;

                        ctx.save();
                        ctx.translate(0, - width * 0.55);
                        let w = w0 + w1 + we + we + gap;
                        ctx.fillText(estr0, -w / 2 + w0 / 2, 0);
                        ctx.fillText(estr1, w / 2 - w1 / 2, 0);

                        ctx.strokeStyle = ctx.fillStyle = "#555";

                        ctx.fillText(eqstr, -w / 2 + w0 + we / 2, 0);
                        ctx.fillText(eqstr, w / 2 - w1 - we / 2, 0);

                        ctx.lineWidth = 1.5;
                        ctx.strokeLine(-w / 2 + w0 + we, - font_size * 0.3,
                            -w / 2 + w0 + we + gap, - font_size * 0.3);

                        ctx.fillStyle = color0;
                        let ww2 = gap * a;
                        ctx.fillRect(-w / 2 + w0 + we + gap / 2 - ww2 / 2, - font_size * 0.1, ww2, font_size * 0.15);

                        ctx.fillStyle = color5;
                        let ww1 = gap * a * ecc;
                        ctx.fillRect(-w / 2 + w0 + we + gap / 2 - ww1 / 2, - font_size * 0.65, ww1, font_size * 0.15);

                        ctx.restore();
                    }

                    ctx.lineWidth = 1.5;

                    ctx.lineCap = "butt";

                    ctx.strokeStyle = "rgba(255, 255, 255, 0.3)"

                    ctx.strokeLine(-a * s, 0, a * s, 0);

                    ctx.strokeLine(c * s, 0, c * s, -(b * 0.3 + 0.15) * s);

                    ctx.strokeLine(0, 0, 0, -(b + 0.15) * s);
                    ctx.strokeLine(a * s, 0, a * s, -(b + 0.15) * s);
                    ctx.lineWidth = 0.015 * s;

                    ctx.lineCap = "butt";
                    ctx.strokeStyle = ctx.fillStyle = color0;
                    ctx.strokeLine(0, -(b + 0.12) * s, a * s, -(b + 0.12) * s);


                    ctx.fillText("semi-major axis", a * s * 0.5, -(b + 0.12) * s - font_size * 0.5);


                    ctx.strokeStyle = ctx.fillStyle = color5;

                    ctx.strokeLine(0, -(b * 0.3 + 0.1) * s, c * s, -(b * 0.3 + 0.1) * s);


                    ctx.lineWidth = 2;

                    ctx.fillStyle = ctx.strokeStyle = color1;
                    ctx.textAlign = "left";
                    ctx.fillText("apoapsis", -width / 2 + font_size + 40, +width / 2 - font_size)

                    ctx.globalAlpha = 0.5;
                    ctx.beginPath();
                    ctx.moveTo(-a * s, 0);
                    ctx.bezierCurveTo((-a - 0.35) * s, 0.35 * s,
                        -width * 0.3, width * 0.3,
                        -width * 0.3, width * 0.5 - font_size * 1.9);
                    ctx.stroke();
                    ctx.globalAlpha = 1;

                    ctx.globalCompositeOperation = "destination-out";
                    ctx.fillEllipse(-a * s, 0, 0.03 * s);
                    ctx.globalCompositeOperation = "source-over";
                    ctx.fillEllipse(-a * s, 0, 0.015 * s);


                    ctx.fillStyle = ctx.strokeStyle = color3;

                    ctx.textAlign = "right";
                    ctx.fillText("periapsis", +width / 2 - font_size - 40, +width / 2 - font_size)

                    ctx.globalAlpha = 0.5;

                    ctx.beginPath();
                    ctx.moveTo(a * s, 0);
                    ctx.bezierCurveTo((a + 0.35) * s, 0.35 * s,
                        width * 0.3, width * 0.3,
                        width * 0.3, width * 0.5 - font_size * 1.9);
                    ctx.stroke();
                    ctx.globalAlpha = 1;

                    ctx.globalCompositeOperation = "destination-out";
                    ctx.fillEllipse(a * s, 0, 0.03 * s);
                    ctx.globalCompositeOperation = "source-over";
                    ctx.fillEllipse(a * s, 0, 0.015 * s);





                    ctx.fillStyle = sphere_gradient(p0[0] * s, p0[1] * s, r0 * s,
                        rgba_hex_color(0xcccccc)
                    );
                    ctx.fillEllipse(p0[0] * s, p0[1] * s, r0 * s);

                    ctx.fillStyle = sphere_gradient(p1[0] * s, p1[1] * s, r1 * s,
                        rgba_hex_color(0x444444)
                    );
                    ctx.fillEllipse(p1[0] * s, p1[1] * s, r1 * s);



                    ctx.strokeStyle = ctx.fillStyle = color4;

                    ctx.textAlign = "center"

                    ctx.fillText("focus points", 0, b * 0.5 * s + font_size * 0.5);

                    ctx.globalAlpha = 0.5;
                    ctx.beginPath();
                    ctx.moveTo(-c * s, s * 0.03);
                    ctx.bezierCurveTo(-c * s, b * 0.3 * s,
                        0, b * 0.1 * s,
                        0, b * 0.5 * s - font_size * 1);
                    ctx.lineTo(0, b * s * 0.5 - font_size * 0.5);
                    ctx.lineTo(0, b * 0.5 * s - font_size * 1);

                    ctx.bezierCurveTo(
                        0, b * 0.1 * s,
                        c * s, b * 0.3 * s,
                        c * s, s * 0.03);
                    ctx.stroke();
                    ctx.globalAlpha = 1;

                    ctx.fillEllipse(c * s, 0, s * 0.015);
                    ctx.fillEllipse(-c * s, 0, s * 0.015);
                }


                if (mode !== "ellipse1") {

                    ctx.fillStyle = sphere_gradient(p0[0] * s, p0[1] * s, r0 * s, c0hex);
                    ctx.fillEllipse(p0[0] * s, p0[1] * s, r0 * s);

                    ctx.fillStyle = sphere_gradient(p1[0] * s, p1[1] * s, r1 * s, c2hex);
                    ctx.fillEllipse(p1[0] * s, p1[1] * s, r1 * s);


                    ctx.lineWidth = 1.5;

                    ctx.strokeStyle = "rgba(255, 255, 255, 0.2)";
                    ctx.strokeLine(p0[0] * s, p0[1] * s, p1[0] * s, p1[1] * s);

                    ctx.strokeStyle = "rgba(255, 255, 255, 0.3)";
                    ctx.fillStyle = "white";
                    ctx.strokeLine(p1[0] * s, p1[1] * s, center[0] * s, center[1] * s);
                    ctx.fillEllipse(center[0] * s, center[1] * s, 0.02 * s);

                }

                let str0;
                let str1;

                if (mode === "ellipse3") {

                    ctx.lineWidth = 2;

                    ctx.strokeStyle = color1;
                    ctx.strokeLine(p0[0] * s, p0[1] * s, p1[0] * s, p1[1] * s);


                    ctx.save();
                    ctx.translate(center[0] * s, center[1] * s);

                    ctx.rotate(state.a);

                    let alpha = slider_args[0];


                    let r0 = a * (1 - ecc * ecc) / (1 + ecc * cos(state.a)) * s * (1 - slide);
                    let r1 = a * (1 - ecc * ecc) / (1 - ecc * cos(state.a + pi)) * s * slide;

                    ctx.globalAlpha = (1 - alpha);
                    ctx.strokeStyle = color3;
                    ctx.strokeLine(0, 0, r0, 0);

                    ctx.globalAlpha = alpha;
                    ctx.strokeLine(0, 0, -r1, 0);
                    ctx.restore();

                    ctx.globalAlpha = 1;

                    let v = Math.sqrt(1 * (2 / r - 1 / a));

                    let w = sqrt(a * (1 - ecc * ecc)) / r / r;


                    str0 = "↺ " + (360 / T).toFixed(3) + "°/s";
                    str1 = "↺ " + (w * 180 / pi / T_scale).toFixed(3) + "°/s";



                }

                draw_barycenter(pb[0] * s, pb[1] * s, 0.02 * s);

                ctx.restore();

                if (mode === "ellipse3") {

                    ctx.fillStyle = color3;
                    ctx.fillText(str0, 0, height / 2);

                    ctx.fillStyle = color1;
                    ctx.fillText(str1, 0, height / 2 + font_size * 1.5);
                }

            } else if (mode.startsWith("sph_sim")) {

                let zoom = 200;

                let capacity = 2048;

                let n = 39 * 39;
                let n_heavy = 0;

                let n_small = 0;
                let n_small_heavy = 0;


                if (mode === "sph_sim3") {
                    n_heavy = ceil(n / 3);
                } if (mode === "sph_sim5") {

                    n = 1200;
                    n_heavy = 400;

                    n_small = 160;
                    n_small_heavy = 53;

                    zoom = 350;
                }

                let sc = width / zoom;

                function drag_to_world(p) {
                    return [(p[0] - 0.5) * zoom, (p[1] - 0.5 / aspect) * zoom];
                }

                function world_to_drag(p) {
                    return [p[0] / zoom + 0.5, p[1] / zoom + 0.5 / aspect];
                }



                const n_small_light = n_small - n_small_heavy;

                const n_big = n - n_small;
                const n_big_heavy = n_heavy - n_small_heavy;
                const n_big_light = n_big - n_big_heavy;

                const n_light = n - n_heavy;

                const small_m = n_small_heavy * 3 + n_small_light;
                const big_m = n_big_heavy * 3 + n_big_light;

                let v_arrow_scale = 0.3;


                function rebuild_sim() {
                    let positions = new Float64Array(n * 2);
                    let velocities = new Float64Array(n * 2);

                    const a = 2.39996323;

                    let a0 = 3.6;
                    let a1 = 0.9;
                    let a2 = 0.2;


                    for (let i = 0; i < n_small; i++) {
                        let x = i / n_small;

                        let pr = a0 * Math.sqrt(x) + a1 * x + a2 * x * x;

                        let theta = a * i + 5;

                        let xx = Math.cos(theta) * pr;
                        let yy = Math.sin(theta) * pr;

                        let write_i = i;
                        if (i >= n_small_heavy) {
                            write_i = n_heavy + i - n_small_heavy;
                        }

                        let vv = 10;

                        positions[2 * write_i + 0] = xx + state.pos[0][0];
                        positions[2 * write_i + 1] = yy + state.pos[0][1];

                        velocities[2 * write_i + 0] = yy * vv + state.vel[0][0];
                        velocities[2 * write_i + 1] = -xx * vv + state.vel[0][1];
                    }

                    let b0 = 7.4;
                    let b1 = 1.2;
                    let b2 = 1.0;

                    for (let i = 0; i < n_big; i++) {
                        let x = i / n_big;

                        let pr = b0 * Math.sqrt(x) + b1 * x + b2 * x * x;


                        let theta = a * i + 5;

                        let xx = Math.cos(theta) * pr;
                        let yy = Math.sin(theta) * pr;

                        let write_i = i + n_small_heavy;
                        if (i >= n_big_heavy) {
                            write_i = n_small + i;
                        }

                        let vv = 10;

                        positions[2 * write_i + 0] = xx;
                        positions[2 * write_i + 1] = yy;

                        velocities[2 * write_i + 0] = yy * vv;
                        velocities[2 * write_i + 1] = -xx * vv;
                    }


                    state.sph.set_initial_values(positions, velocities, n_heavy);


                }

                if (!state) {
                    state = {};

                    let positions;
                    let velocities;

                    function shuffle(a, n) {

                        for (let i = n - 1; i > 0; i--) {
                            let j = Math.floor(Math.random() * (i + 1));
                            let x = a[i * 2];
                            let y = a[i * 2 + 1];
                            a[i * 2] = a[j * 2];
                            a[i * 2 + 1] = a[j * 2 + 1];
                            a[j * 2] = x;
                            a[j * 2 + 1] = y;
                        }
                        return a;
                    }

                    if (mode === "sph_sim1" || mode === "sph_sim2" || mode === "sph_sim3") {

                        let nx = 35;
                        let ny = 35;
                        let n = nx * ny;

                        positions = new Float64Array(n * 2);

                        let i = 0;
                        for (let y = 0; y < ny; y++) {
                            for (let x = 0; x < nx; x++) {
                                positions[2 * i + 0] = ((x + random() * 0.8 + 0.1) / nx * 2 - 1) * zoom * 0.5;
                                positions[2 * i + 1] = ((y + random() * 0.8 + 0.1) / ny * 2 - 1) * zoom * 0.5;
                                i++;
                            }
                        }

                        if (mode === "sph_sim3")
                            shuffle(positions, n);

                        if (mode === "sph_sim2" || mode === "sph_sim3") {
                            velocities = new Float64Array(n * 2);

                            let ww = random() * 0.2 + 0.2;
                            let vx = 0;
                            let vy = 0;
                            for (let i = 0; i < n; i++) {
                                let vvx = 150 * (random() * 2 - 1);
                                let vvy = 150 * (random() * 2 - 1);

                                vvy += -positions[2 * i + 0] * ww;

                                vx += vvx
                                vy += vvy

                                velocities[2 * i + 0] = vvx;
                                velocities[2 * i + 1] = vvy;
                            }

                            vx /= n;
                            vy /= n;

                            for (let i = 0; i < n; i++) {
                                velocities[2 * i + 0] -= vx;
                                velocities[2 * i + 1] -= vy;
                            }
                        }
                    }


                    state.sph = new SPHSim(capacity);

                    state.sph.set_initial_values(positions, velocities, n_heavy);
                    state.blob_buffer = new Float32Array(2048 * 2);

                    if (mode === "sph_sim5") {

                        state.pos = [[-50, 11.8]];
                        state.vel = [[388, 0.0]];
                        state.radii = [6];
                        state.count = 1;

                        play_button.hidden = false;
                        reset_button.hidden = true;

                        this.set_paused(true);

                        drag_enabled = true;

                        state.initial_pos = [state.pos[0]];
                        state.ddt = 0;
                        state.state = 0;


                        if (draggables.length) {

                            for (let i = 0; i < state.count; i++)
                                state.vel[i] = vec_scale(vec_sub(drag_to_world(draggables[2 * i + 1].pos), drag_to_world(draggables[2 * i + 0].pos)), 1 / v_arrow_scale);
                        }

                        rebuild_sim();
                    } else {
                        self.set_paused(false);
                    }
                }

                if (draggables.length == 0) {

                    if (mode === "sph_sim5") {
                        draggables = [
                            { pos: world_to_drag(state.pos[0]), size: 0.035 },
                            { pos: world_to_drag(state.pos[0]), size: 0.035 }]
                    }
                }



                if (state.state == 0) {
                    if (self.paused) {
                        if (dragged_index >= 0) {
                            let i = (dragged_index & 14) >> 1;
                            if ((dragged_index & 1) == 0) {
                                state.pos[i] = drag_to_world(draggables[dragged_index].pos);
                                draggables[dragged_index + 1].pos = world_to_drag(vec_add(state.pos[i], vec_scale(state.vel[i], v_arrow_scale)));


                            } else {
                                state.vel[i] = vec_scale(vec_sub(drag_to_world(draggables[dragged_index].pos), state.pos[i]), 1 / v_arrow_scale);
                            }



                        } else {
                            for (let i = 0; i < state.count; i++) {
                                state.pos[i] = drag_to_world(draggables[2 * i + 0].pos);
                                draggables[2 * i + 1].pos = world_to_drag(vec_add(state.pos[i], vec_scale(state.vel[i], v_arrow_scale)));
                            }
                        }

                        rebuild_sim();


                    } else {
                        play_button.hidden = true;
                        reset_button.hidden = false;
                        this.set_paused(false);

                        canvas.style.cursor = "default";
                        drag_enabled = false;

                        state.state = 1;
                    }
                }


                let sph = state.sph;

                let n_steps = min(max(1, round(dt * 120)), 4);

                if (mode === "sph_sim5" && state.state == 0)
                    n_steps = 0;

                for (let i = 0; i < n_steps; i++)
                    sph.step();

                gl.begin(width, height);

                for (let i = 1; i < sph.n; i++) {
                    let x = sph.positions[2 * i + 0];
                    let y = sph.positions[2 * i + 1];
                    state.blob_buffer[2 * i - 2] = x;
                    state.blob_buffer[2 * i - 1] = y;
                }

                let params = {
                    color0: rgba_hex_color(0x296CBF),
                    color1: rgba_hex_color(0xD5B034),
                    n_threshold: n_heavy,
                    size: 2.5 * sc,
                };

                let mvp = scale_mat4([2 / zoom, -2 * aspect / zoom, 1]);

                gl.set_blend_enabled(true);
                gl.update_blob_buffer(state.blob_buffer);
                gl.draw_blobs(mvp, sph.n - 1, params);

                ctx.drawImage(gl.finish(), 0, 0, width, height);

                ctx.translate(width / 2, height / 2);

                ctx.scale(sc, sc);

                if (mode === "sph_sim5" && state.state == 0) {
                    let i = 0;
                    let off = 3;


                    let col = rgba_hex_color(0xD5B034);
                    col = vec_mul(col, [0.8, 0.8, 0.8, 1.0]);
                    let col2 = vec_mul(col, [0.6, 0.6, 0.6, 0.8]);

                    ctx.strokeStyle = rgba_color_string(col);
                    ctx.fillStyle = rgba_color_string(col2);
                    ctx.lineCap = "butt";
                    ctx.lineWidth = 1.5 / sc;

                    let dir = vec_norm(state.vel[i]);

                    let len = vec_len(state.vel[i]) * v_arrow_scale - 2 * (state.radii[i] + off);

                    if (len > 0) {
                        ctx.arrow(state.pos[i][0] + dir[0] * (state.radii[i] + off),
                            state.pos[i][1] + dir[1] * (state.radii[i] + off),
                            state.pos[i][0] + state.vel[i][0] * v_arrow_scale - dir[0] * (state.radii[i] + off),
                            state.pos[i][1] + state.vel[i][1] * v_arrow_scale - dir[1] * (state.radii[i] + off),
                            min(1.5 * sc, sc * len * 0.1),
                            min(5.25 * sc, sc * len * 0.35),
                            min(7.5 * sc, sc * len * 0.5)
                        );

                        ctx.fill();
                        ctx.stroke();
                    }

                    ctx.globalAlpha = 0.5;
                    let c = 2 * pi * state.radii[i];
                    ctx.setLineDash([c / 20, c / 20]);
                    ctx.strokeEllipse(state.pos[i][0] + state.vel[i][0] * v_arrow_scale,
                        state.pos[i][1] + state.vel[i][1] * v_arrow_scale, state.radii[i]);
                    ctx.setLineDash([]);
                    ctx.globalAlpha = 1.0;
                }


                ctx.feather(width * scale, height * scale,
                    canvas.height * 0.1, canvas.height * 0.1,
                    canvas.height * 0.1, canvas.height * 0.1);

            } else if (mode.startsWith("tides3d")) {

                let inclination = 0.0;

                let has_arrows = false;
                let has_plot = true;
                let has_figurine = true;

                let p0_strength = 0.2;

                if (mode === "tides3d1" || mode === "tides3d2") {
                    p0_strength = 0.0;
                    has_plot = false;
                    has_figurine = false;
                    has_arrows = true;
                } else if (mode === "tides3d7") {
                    inclination = 0.5;
                }

                if (!state) {
                    state = {};
                    state.t = 0;
                    state.lat = 0.6;
                    state.lon = 0;

                    let fi = 0.5 * (1 + Math.sqrt(5));
                    let a = (2.0 - fi) * 2.0 * Math.PI;

                    let n_rand_vertices = 60;
                    let rand_vertices = [];

                    if (mode === "tides3d1")
                        rand_vertices.push([0, 0, 0]);

                    for (let i = 1; i < n_rand_vertices; i++) {
                        /* Jiggle a little so that it avoids grid-like bands of rays. */
                        let lat = Math.asin(-1 + 2 * i / n_rand_vertices) + Math.random() * 0.05;
                        let lon = a * i + Math.random() * 0.08;

                        let x = Math.cos(lon) * Math.cos(lat);
                        let y = Math.sin(lon) * Math.cos(lat);
                        let z = Math.sin(lat);

                        rand_vertices.push([x, y, z]);
                    }

                    state.rand_vertices = rand_vertices;


                }

                dt *= slider_args[0] * slider_args[0];

                state.t += dt;
                let t = state.t;

                function big_rot(t) {
                    return t * 10
                }

                function small_anomaly(t) {
                    return t * 0.5;
                }

                let fov = pi * 0.05;
                let near = 1.0;
                let far = 30.0;
                let f = 1.0 / Math.tan(fov / 2);
                let rangeInv = 1 / (near - far);

                proj = [
                    f, 0, 0, 0,
                    0, f, 0, 0,
                    0, 0, (near + far) * rangeInv, -1,
                    0, 0, near * far * rangeInv * 2, 0
                ];


                let mvp = mat3_to_mat4(rot);
                mvp = mat4_mul(translation_mat4([0, 0, -29.5]), mvp);
                mvp = mat4_mul(proj, mvp);



                let earth_mat = mat4_mul(mvp, rot_z_mat4(big_rot(t)));

                let lat = state.lat;
                let lon = state.lon;


                if (has_figurine) {



                    if (draggables.length == 0)
                        draggables = [{
                            pos: world_to_drag_sphere(lat, lon, 1.15, earth_mat), size: 0.1, limiter: sphere_limiter
                        }];


                    if (dragged_index >= 0) {

                        let lat_lon = drag_to_world_sphere(draggables[0].pos, 1.15, mat4_invert(earth_mat));

                        lat = state.lat = lat_lon[0];
                        lon = state.lon = lat_lon[1];
                    } else {
                        draggables[0].pos = world_to_drag_sphere(lat, lon, 1.15, earth_mat);
                    }
                }


                let local_observer_pos = [cos(lat) * cos(lon), cos(lat) * sin(lon), sin(lat)];


                let small_a = 4;

                gl.begin(width, width);
                gl.set_depth_test_enabled(true);
                gl.set_cull_face_enabled(true);

                {
                    let mat = scale_mat4(1);
                    mat = mat4_mul(rot_z_mat4(big_rot(t)), mat);
                    mat = mat4_mul(mvp, mat);

                    let r = mat3_mul(rot, rot_z_mat3(big_rot(t)));

                    gl.draw_simple("proto", mat, r, { color: rgba_hex_color(color3h) });

                }



                let p0 = [
                    small_a * cos(small_anomaly(t)),
                    small_a * sin(small_anomaly(t)),
                    -0
                ];

                p0 = mat3_mul_vec(rot_x_mat3(inclination), p0);



                if (has_figurine) {
                    gl.set_cull_face_enabled(false);

                    let figurine_mat = scale_mat4(0.04);
                    figurine_mat = mat4_mul(rot_y_mat4(pi / 2), figurine_mat);
                    figurine_mat = mat4_mul(translation_mat4([1.166, 0, 0]), figurine_mat);
                    figurine_mat = mat4_mul(rot_y_mat4(-lat), figurine_mat);
                    figurine_mat = mat4_mul(rot_z_mat4(lon), figurine_mat);
                    figurine_mat = mat4_mul(earth_mat, figurine_mat);

                    let figurine_rot = rot_y_mat3(pi / 2);
                    figurine_rot = mat3_mul(rot_y_mat3(-lat), figurine_rot);
                    figurine_rot = mat3_mul(rot_z_mat3(lon), figurine_rot);
                    figurine_rot = mat3_mul(rot_z_mat3(big_rot(t)), figurine_rot);
                    figurine_rot = mat3_mul(rot, figurine_rot);

                    draw_figurine(gl, figurine_mat, figurine_rot, 0, 0);

                    gl.set_cull_face_enabled(true);

                }

                let l_scale = 3;


                if (has_arrows) {

                    let pc = vec_scale(p0, l_scale);
                    let dcl = vec_len(pc);
                    let fc = vec_scale(pc, 1 / (dcl * dcl * dcl));


                    let diff = mode === "tides3d2";



                    let n = state.rand_vertices.length;
                    for (let i = 0; i < n; i++) {

                        let p = state.rand_vertices[i];

                        let params = {};
                        params.color = rgba_hex_color(0xbbbbbb);


                        let dp = vec_sub(pc, p);
                        let dpl = vec_len(dp);
                        let f = vec_scale(dp, 1 / (dpl * dpl * dpl));

                        let sc = 3.5 * vec_len(f);

                        if (diff) {
                            params.color = rgba_hex_color(color0h);
                            f = vec_sub(f, fc);
                            sc = 25 * vec_len(f);
                        }

                        let x = vec_norm(f);
                        let y = vec_norm(vec_cross(x, [0, 0, 1]));
                        let z = vec_cross(x, y);

                        let m = [
                            x[0], y[0], z[0],
                            x[1], y[1], z[1],
                            x[2], y[2], z[2]];

                        m = mat3_mul(m, rot_y_mat3(pi / 2));


                        let mat = translation_mat4([0, 0, 10]);
                        mat = mat4_mul(mat3_to_mat4(m), mat);
                        mat = mat4_mul(scale_mat4(sc), mat);
                        mat = mat4_mul(translation_mat4(vec_scale(p, 1.25)), mat);
                        mat = mat4_mul(mvp, mat);

                        let r = m;
                        r = mat3_mul(rot, r);


                        if (!diff && i == 0) {
                            gl.set_depth_test_enabled(false);
                            gl.set_depth_write_enabled(false);
                            params.color = rgba_hex_color(color5h);
                            gl.draw_simple("arrow", mat, r, params);
                            gl.set_depth_test_enabled(true);
                            gl.set_depth_write_enabled(true);

                        } else {
                            gl.draw_simple("arrow", mat, r, params);

                        }


                    }
                }


                {
                    let mat = scale_mat4(0.1);
                    mat = mat4_mul(rot_z_mat4(small_anomaly(t)), mat);
                    mat = mat4_mul(translation_mat4(p0), mat);
                    mat = mat4_mul(mvp, mat);

                    let r = mat3_mul(rot, rot_z_mat3(small_anomaly(t)));

                    let c = rgba_hex_color(color1h);
                    c[3] = 0.2;
                    gl.draw_simple("proto", mat, r, { color: c, params: [0.4, 1.1, 1.2, 1] });
                }

                gl.set_depth_write_enabled(false);
                gl.set_blend_enabled(true);

                let orbit_mat = mat4_mul(mvp, rot_x_mat4(inclination));

                gl.draw_ellipse(orbit_mat, rot, rgba_hex_color(color0h, 0.1), small_a, 0, 0.008);


                {
                    let color = vec_scale([1, 1, 1, 1], 0.2);

                    let e_ap0 = [0, 0, 1.1];
                    let e_ap1 = [0, 0, 1.3];

                    gl.draw_segment(mvp, rot, color, e_ap0, e_ap1, 0.01);

                    e_ap0 = [0, 0, -1.1];
                    e_ap1 = [0, 0, -1.3];

                    gl.draw_segment(mvp, rot, color, e_ap0, e_ap1, 0.01);
                }

                {
                    let mat = scale_mat4(p0_strength != 0.0 ? 1.2 : 1.3);
                    mat = mat4_mul(mvp, mat);

                    let pp0 = vec_norm(p0);

                    pp0.push(p0_strength);
                    let params = {
                        color: rgba_hex_color(0x5297C9, 0.2),
                        p0: pp0,
                    };
                    gl.draw_simple("tidal_water", mat, rot, params);

                }




                if (has_plot) {
                    ctx.save();
                    let hh = height * 0.15;

                    ctx.translate(0, height - hh * 0.5);

                    let n = ceil(width);


                    ctx.fillStyle = "#2D506A";
                    ctx.strokeStyle = "#3C6B8D";
                    ctx.lineWidth = 2;
                    ctx.globalAlpha = 0.5;

                    ctx.beginPath();
                    ctx.lineTo(-width * 0.5, hh * 0.25);

                    let len = 6.0;
                    let offset = 3.0;

                    for (let i = 0; i < n + 4; i++) {

                        let tt = i / n;
                        let t = state.t + tt * len - offset;;

                        let observer_pos = mat3_mul_vec(rot_z_mat3(big_rot(t)), local_observer_pos);

                        let p0 = [small_a * cos(small_anomaly(t)),
                        small_a * sin(small_anomaly(t)), 0];

                        p0 = mat3_mul_vec(rot_x_mat3(inclination), p0);
                        p0 = vec_norm(p0);

                        let x = p0;
                        let y = vec_norm(vec_cross(p0, [0, 0, 1]));
                        let z = vec_cross(x, y);

                        let mat = [
                            x[0], y[0], z[0],
                            x[1], y[1], z[1],
                            x[2], y[2], z[2]];

                        let lp = mat3_mul_vec(mat3_transpose(mat), observer_pos);

                        let th = acos(lp[2]);
                        let fi = acos(lp[0] / sqrt(lp[0] * lp[0] + lp[1] * lp[1]));

                        let a = 2;

                        lp[0] = a * sin(th) * cos(fi);

                        let h = vec_len(lp) - 1.0;

                        ctx.lineTo(tt * width, -h * hh * 0.25);

                    }

                    ctx.lineTo(width * 1.5, hh * 0.25);


                    ctx.fill();
                    ctx.stroke();

                    ctx.globalAlpha = 0.5;
                    ctx.fillStyle = color3;
                    ctx.fillRect(0, hh * 0.25 - 0.25, width, hh);


                    let x = offset / len * width;

                    ctx.globalAlpha = 0.4;


                    ctx.globalCompositeOperation = "destination-over";
                    ctx.globalAlpha = 1.0;

                    let w = width * 0.0095;

                    ctx.translate(x, hh * 0.25);
                    ctx.lineWidth = w * 1.2;
                    ctx.strokeStyle = ctx.fillStyle = "#D02828";
                    ctx.strokeLine(+w * 0.7, -w * 0.5, +w * 0.7, -hh * 0.48);
                    ctx.strokeLine(-w * 0.7, -w * 0.5, -w * 0.7, -hh * 0.48);
                    ctx.strokeLine(0, -hh * 0.25, 0, -hh * 0.48);
                    ctx.strokeLine(-w * 1.6, -hh * 0.48, +w * 1.6, -hh * 0.48);

                    ctx.lineWidth = w * 1;
                    ctx.strokeLine(-w * 1.9, -hh * 0.29, -w * 1.7, -hh * 0.48);
                    ctx.strokeLine(+w * 1.9, -hh * 0.29, +w * 1.7, -hh * 0.48);


                    ctx.fillEllipse(0, -hh * 0.5 - w * 1.2, w * 1.);

                    ctx.feather(width * scale, height * scale,
                        canvas.height * 0.05, canvas.height * 0.05,
                        canvas.height * 0.05, canvas.height * 0.05);

                    ctx.restore();
                    ctx.globalCompositeOperation = "destination-over"
                }



                ctx.drawImage(gl.finish(), 0, 0, width, width);

            } else if (mode.startsWith("tides")) {




                let n_big = 1700;
                let n_small = 300;

                let d_big_rot = -1;
                let d_small_rot = -1;
                let d_small_anomaly = -0.2;

                let draw_arrows = true;
                let tidal_arrows = true;
                let draw_em_line = true;
                let draw_m_axis = true;

                let small_a = 90;

                let stretch = 1.02;
                let lag = 0.01;

                let three_bodies = false;

                let zoom_t = slider_args[0];

                if (mode === "tides1" || mode === "tides2") {
                    draw_arrows = false;
                    draw_em_line = false;
                    draw_m_axis = false;
                } else if (mode === "tides3" || mode === "tides4" || mode === "tides4a") {
                    n_small = 0;
                    draw_arrows = false;
                    draw_em_line = false;
                    draw_m_axis = false;
                    three_bodies = true;
                    zoom_t = 0;
                } else if (mode === "tides5") {
                    draw_m_axis = false;
                    tidal_arrows = false;

                } else if (mode === "tides5a") {
                    draw_m_axis = false;

                } else if (mode === "tides6") {
                    draw_m_axis = false;
                    stretch = 1 + 0.3 * slider_args[1];

                } else if (mode === "tides7") {
                    stretch = 1.3;
                    lag = 0.5 * slider_args[1];
                }

                let zoom = 200;
                zoom *= lerp(1, 0.1, zoom_t);

                let sc = width / zoom;


                if (!state) {
                    state = {};
                    state.big_rot = 0;
                    state.small_rot = 0;
                    state.small_anomaly = 0;


                    if (three_bodies) {
                        state.pos = [142, 155, 168];
                        state.vel = [0, 0, 0];

                        if (mode === "tides3")
                            self.set_paused(false);
                    }
                }

                if (mode === "tides4" || mode === "tides4a") {
                    let d = 50 * (1 - slider_args[0]);
                    state.pos = [142 - d, 155 - d, 168 - d];
                }


                state.big_rot += d_big_rot * dt;
                state.small_rot += d_small_rot * dt;
                state.small_anomaly += d_small_anomaly * dt;

                if (three_bodies) {


                    for (let i = 0; i < 3; i++) {

                        let r = state.pos[i];
                        let a = -10.5 * n_big * 1 / (r * r);

                        for (let j = 0; j < 3; j++) {

                            if (i == j)
                                continue;

                            let r = state.pos[i] - state.pos[j];
                            a + 1 / (r * r);

                        }

                        state.vel[i] += a * dt;
                        state.pos[i] += state.vel[i] * dt;

                        state.pos[i] = state.pos[i] > 0 ? state.pos[i] : 0;
                    }



                }

                let sx = small_a * cos(state.small_anomaly);
                let sy = small_a * sin(state.small_anomaly);


                let tx = -sx * zoom_t;
                let ty = -sy * zoom_t;

                if (three_bodies) {
                    tx -= 80;

                    if (mode == "tides4")
                        ty += 20;
                }


                gl.begin(width, height);


                let mvp = scale_mat4([2 / zoom, -2 * aspect / zoom, 0.01]);
                mvp = mat4_mul(mvp, translation_mat4([tx, ty, 0]));

                {
                    let mat = scale_mat4(15);
                    mat = mat4_mul(rot_z_mat4(state.big_rot), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_simple("proto", mat, ident_mat3, { color: rgba_hex_color(0x4676A9) });

                }

                if (!three_bodies) {
                    let mat = scale_mat4(4);
                    mat = mat4_mul(rot_z_mat4(state.small_anomaly + state.small_rot), mat);
                    mat = mat4_mul(scale_mat4([stretch, 1, 1]), mat);
                    mat = mat4_mul(rot_z_mat4(state.small_anomaly - lag), mat);
                    mat = mat4_mul(translation_mat4([sx, sy, 0]), mat);
                    mat = mat4_mul(mvp, mat);

                    gl.draw_simple("proto", mat, ident_mat3, { color: [0.5, 0.5, 0.5, 0.5] });

                }

                ctx.drawImage(gl.finish(), 0, 0, width, height);


                ctx.translate(width / 2, height / 2);

                ctx.scale(sc, sc);
                ctx.translate(tx, ty);

                ctx.lineWidth = 0.3;

                if (three_bodies) {

                    ctx.globalCompositeOperation = "destination-over";
                    let colors = [color4, color0, color2];
                    let colorsh = [color4h, color0h, color2h];

                    let r = 1.8;

                    for (let i = 0; i < 3; i++) {

                        ctx.fillStyle = sphere_gradient(state.pos[i], 0, r,
                            rgba_hex_color(colorsh[i])
                        );

                        ctx.fillEllipse(state.pos[i], 0, r);
                    }

                    r = 1.5;
                    let dash_length = 2 * pi * r / 8;

                    ctx.setLineDash([dash_length * 0.3, dash_length * 0.7]);

                    for (let i = 0; i < 3; i++) {

                        ctx.strokeStyle = colors[i];
                        ctx.strokeEllipse(state.pos[1] + 13 * (i - 1), 0, r);
                    }

                    ctx.setLineDash([]);

                    if (mode === "tides4" || mode === "tides4a") {

                        let g = 140000;

                        if (mode == "tides4") {

                            ctx.strokeStyle = "#333";
                            ctx.strokeLine(0, 0, 200, 0);
                            ctx.strokeLine(0, 0, 0, -200);

                            ctx.lineWidth = 0.6;
                            ctx.strokeStyle = "#aaa"
                            let n = 100;
                            ctx.beginPath();
                            for (let i = 0; i < n; i++) {
                                let x = 12 + i * 2;
                                let f = g / (x * x);
                                ctx.lineTo(x, -f);
                            }

                            ctx.stroke();
                        }

                        ctx.globalCompositeOperation = "source-over";

                        for (let i = 0; i < 3; i++) {

                            ctx.strokeStyle = ctx.fillStyle = colors[i];
                            let x = state.pos[i];
                            let y = -g / (x * x);
                            ctx.globalAlpha = 0.3;
                            ctx.lineWidth = 0.6;

                            if (mode == "tides4") {

                                ctx.strokeLine(x, 0, x, y);
                                ctx.globalAlpha = 1;
                                ctx.fillEllipse(x, y, 0.4);
                            } else {
                                let x1 = state.pos[1];
                                y += g / (x1 * x1);
                                y *= 8;
                            }
                            ctx.globalAlpha = 1;


                            if (mode == "tides4") {
                                ctx.lineWidth = 0.4;
                                ctx.fillStyle = "#ddd";
                                ctx.strokeStyle = "#222";
                            } else {
                                ctx.lineWidth = 0.35;
                                ctx.fillStyle = color0;
                                ctx.strokeStyle = "#111";

                            }
                            ctx.arrow(x, 0, x + y, 0, 1, 3, 4);
                            ctx.fill();
                            ctx.stroke();
                        }

                    }
                }

                ctx.fillStyle = "red";

                if (draw_arrows) {
                    let c0 = rgba_hex_color(color4h);
                    let c1 = rgba_hex_color(color0h);
                    let c2 = rgba_hex_color(color2h);

                    let ca = cos(state.small_anomaly - lag);
                    let sa = sin(state.small_anomaly - lag);

                    let sx = small_a * cos(state.small_anomaly);
                    let sy = small_a * sin(state.small_anomaly);

                    const a = 2.39996323;

                    const g = 8000;

                    let n = 30;

                    let s2 = sx * sx + sy * sy;
                    let s = sqrt(s2);
                    let f0x = -g * sx / (s2 * s);
                    let f0y = -g * sy / (s2 * s);

                    for (let i = 0; i < n; i++) {
                        let x = i / n;
                        let pr = 3.8 * Math.sqrt(x) + 0.1;
                        let theta = a * i + state.small_rot;

                        let xr = Math.cos(theta + lag) * pr;
                        let yr = Math.sin(theta + lag) * pr;

                        let xr2 = ca * xr - sa * yr;
                        let yr2 = sa * xr + ca * yr;

                        xr2 *= stretch;

                        let x0 = ca * xr2 - sa * yr2 + sx;
                        let y0 = sa * xr2 + ca * yr2 + sy;

                        let r2 = x0 * x0 + y0 * y0;

                        let r = sqrt(r2);
                        let fgx = -g * x0 / (r2 * r);
                        let fgy = -g * y0 / (r2 * r);

                        if (tidal_arrows) {
                            fgx -= f0x;
                            fgy -= f0y;

                            fgx *= 20;
                            fgy *= 20;
                        }


                        let x1 = x0 + fgx;
                        let y1 = y0 + fgy;

                        let t = (r - 86) / 8;

                        let c = t < 0.5 ? vec_lerp(c0, c1, 2 * t) : vec_lerp(c1, c2, 2 * t - 1);
                        ctx.lineWidth = 0.06;

                        ctx.fillStyle = "#777"
                        ctx.strokeStyle = "#222"

                        ctx.fillEllipse(x0, y0, 0.13);
                        ctx.strokeEllipse(x0, y0, 0.13);

                        ctx.lineWidth = 0.06;
                        if (tidal_arrows) {
                            ctx.fillStyle = color0;
                            ctx.strokeStyle = "#111";
                        } else {
                            ctx.fillStyle = i == 0 ? color5 : "#ddd";
                            ctx.strokeStyle = "#222";
                        }

                        let s = min(1.0, sqrt(fgx * fgx + fgy * fgy) * 1);

                        ctx.arrow(x0, y0, x1, y1, 0.2 * s, 0.6 * s, 0.75 * s);
                        ctx.fill();
                        ctx.stroke();
                    }
                }


                ctx.save();
                ctx.translate(sx, sy);
                ctx.rotate(-lag + state.small_anomaly);

                if (draw_m_axis) {

                    ctx.lineWidth = 0.005 * zoom;

                    ctx.strokeStyle = color3;

                    ctx.globalCompositeOperation = "destination-over";
                    ctx.strokeLine(-10, 0, 10, 0);
                }

                ctx.restore();



                if (draw_em_line) {
                    let w = 0.003 * zoom;
                    ctx.lineWidth = w;
                    ctx.lineCap = "butt";
                    ctx.strokeStyle = "#333";


                    ctx.globalCompositeOperation = "destination-over";
                    ctx.strokeLine(0, 0, sx, sy);
                    ctx.globalCompositeOperation = "source-over";
                }



                ctx.feather(width * scale, height * scale,
                    canvas.height * 0.05, canvas.height * 0.05,
                    canvas.height * 0.05, canvas.height * 0.05);
            } else if (mode === "em_mesh") {


                if (!state) {
                    state = {};
                    state.t = 0;
                }


                let f = lerp(20, 40, slider_args[0]);
                state.t += dt * f * 0.3;

                let tt = state.t;
                let mvp = mat4_mul(proj, mat3_to_mat4(rot));
                mvp = mat4_mul(mvp, scale_mat4(1.8));

                gl.begin(width, height);

                let l = 1.0 - saturate(3.0 * sin(tt * 0.25 - 0.4));
                gl.draw_simple("sphere", mat4_mul(mvp, scale_mat4(0.12)), ident_mat3, { color: [l, l, l, 1] });

                gl.set_depth_test_enabled(true);
                gl.set_depth_write_enabled(false);
                gl.set_blend_enabled(true);

                gl.set_blend_mode("plusl");

                gl.draw_mesh(mvp, [f, tt, 0, 0]);

                ctx.drawImage(gl.finish(), 0, 0, width, height);

                ctx.strokeStyle = "rgba(255,255,255,0.2)";

                let r = width * 0.056;
                ctx.setLineDash([r * 0.03 * pi, r * 0.06 * pi]);
                ctx.strokeEllipse(width / 2, height / 2, r);

            } else if (mode.startsWith("em")) {


                let h = height;
                let w = width;

                let f = lerp(20, 40, slider_args[0]);

                let a = slider_args[1] * pi;
                let m = slider_args[2];

                if (mode === "em4") {
                    m = 3;
                } else if (mode === "em5") {
                    a = slider_args[0] * pi;
                    m = 3;

                    f = 40;
                }

                if (!state) {
                    state = {};
                    state.t = 0;
                }


                state.t += dt * f * 0.3;

                let tt = state.t;


                if (draggables.length == 0) {

                    function limiter(p) {
                        p[0] = clamp(p[0], 0.08, 0.38);
                        p[1] = clamp(p[1], 0.08, 0.38);
                        return p;
                    }

                    draggables = [{ pos: [0.15, 0.2], size: 0.035, limiter: limiter }];

                    if (mode === "em3" || mode === "em4" || mode === "em4a" || mode === "em5") {
                        draggables.push({ pos: [0.24, 0.3], size: 0.035, limiter: limiter });
                    }
                }


                let aspect = width / h;

                let p0x = draggables[0].pos[0] * aspect * 2 - 1;
                let p0y = -draggables[0].pos[1] * aspect * 2 + 1;

                let p1x;
                let p1y;

                if (draggables.length > 1) {
                    p1x = draggables[1].pos[0] * aspect * 2 - 1;
                    p1y = -draggables[1].pos[1] * aspect * 2 + 1;
                }

                let ci = cos(a);
                let si = sin(a);



                let off = 0.2;
                let li0 = (p0x * si + p0y * ci);
                let li1 = (p1x * si + p1y * ci);
                let li = max(li0, li1) + off;
                li0 = li - li0;
                li1 = li - li1;

                let lo0 = p1x;
                let lo1 = p0x;
                let lo = max(lo0, lo1) + 0.2;

                lo0 = 0.9 - (lo - lo0);
                lo1 = 0.9 - (lo - lo1);

                let mid_l = sqrt((p0x - p1x) * (p0x - p1x) + (p0y - p1y) * (p0y - p1y));


                let cap = 0.2;
                let cap_end = 1.6;

                let total_l = cap + max(li0, li1) + mid_l + max(lo0, lo1) + cap_end;



                let params0 = {};

                params0.dir0 = [0, 0, 0, 0];
                params0.dir1 = [0, 0, 0, 0];
                params0.dir2 = [0, 0, 0, 0];
                params0.dir3 = [0, 0, 0, 0];
                params0.p0 = [0, 0, 0, 0];
                params0.p1 = [0, 0, 0, 0];
                params0.p2 = [0, 0, 0, 0];
                params0.p3 = [0, 0, 0, 0];
                params0.params = [f, tt, 0, 0];

                let params1 = {};

                params1.dir0 = [0, 0, 0, 0];
                params1.dir1 = [0, 0, 0, 0];
                params1.dir2 = [0, 0, 0, 0];
                params1.dir3 = [0, 0, 0, 0];
                params1.p0 = [0, 0, 0, 0];
                params1.p1 = [0, 0, 0, 0];
                params1.p2 = [0, 0, 0, 0];
                params1.p3 = [0, 0, 0, 0];
                params1.params = [f, tt, 0, 0];



                if (mode === "em1") {
                    params0.p0 = [p0x, p0y, 0.8, 0];

                    params1.dir0 = [1, 0, 0.3, -p0x * f];

                } else if (mode === "em2") {
                    params0.dir0 = [-sin(a), -cos(a), 0.8, 0];

                    {
                        params0.p0 = [p0x, p0y, 0.4, (-sin(a) * p0x - cos(a) * p0y) * f];

                        params1.dir0 = [1, 0, 0.2, (-sin(a) * p0x - cos(a) * p0y - p0x) * f];
                    }

                } else if (mode === "em3") {
                    params0.dir0 = [-sin(a), -cos(a), 0.8, 0];

                    {
                        params0.p0 = [p0x, p0y, 0.4, (-sin(a) * p0x - cos(a) * p0y) * f];
                        params0.p1 = [p1x, p1y, 0.4, (-sin(a) * p1x - cos(a) * p1y) * f];

                        params1.dir0 = [1, 0, 0.2, (-sin(a) * p0x - cos(a) * p0y - p0x) * f];
                        params1.dir1 = [1, 0, 0.2, (-sin(a) * p1x - cos(a) * p1y - p1x) * f];
                    }
                } else if (mode === "em4" || mode === "em4a" || mode === "em5") {
                    if (m == 0 || m == 3)
                        params0.dir0 = [-sin(a), -cos(a), 0.8, 0];

                    if (m == 1 || m == 3) {
                        params0.p0 = [p0x, p0y, 0.4, (-sin(a) * p0x - cos(a) * p0y) * f];
                        params0.p1 = [p1x, p1y, 0.4, (-sin(a) * p1x - cos(a) * p1y) * f];

                        params1.dir0 = [1, 0, 0.2, (-sin(a) * p0x - cos(a) * p0y - p0x) * f];
                        params1.dir1 = [1, 0, 0.2, (-sin(a) * p1x - cos(a) * p1y - p1x) * f];
                    }
                    if (m == 2 || m == 3) {

                        let da = sqrt((p0x - p1x) * (p0x - p1x) + (p0y - p1y) * (p0y - p1y));

                        params0.p2 = [p0x, p0y, 0.4, (-sin(a) * p1x - cos(a) * p1y + da) * f];
                        params0.p3 = [p1x, p1y, 0.4, (-sin(a) * p0x - cos(a) * p0y + da) * f];

                        params1.dir2 = [1, 0, 0.2, (-sin(a) * p1x - cos(a) * p1y + da - p0x) * f];
                        params1.dir3 = [1, 0, 0.2, (-sin(a) * p0x - cos(a) * p0y + da - p1x) * f];
                    }

                    if (mode === "em5") {
                        params0.params[1] = params1.params[1] = (slider_args[1] * total_l - li - cap) * f;
                        params0.dir0[2] = 1.0 - smooth_step(max(li0, li1) + cap + 0.05,
                            max(li0, li1) + cap + 0.1,
                            slider_args[1] * total_l);
                        params0.p1[2] = 1.0 - smooth_step(li1 + cap + mid_l + 0.1,
                            li1 + cap + mid_l + 0.2,
                            slider_args[1] * total_l);
                        params0.p0[2] = 1.0 - smooth_step(li0 + cap + mid_l + 0.1,
                            li0 + cap + mid_l + 0.2,
                            slider_args[1] * total_l);

                        params1.dir0[2] = 0;
                        params1.dir1[2] = 0;

                        params1.dir2[3] += 2.43 * f;
                        params1.dir3[3] += 2.43 * f;
                        params0.params[2] = params1.params[2] = 1;
                        params0.params[3] = params1.params[3] = 0.5 / pi;
                    }

                    if (mode === "em4a") {
                        params0.params[2] = params1.params[2] = 2;
                    }
                }

                {
                    gl.begin(width, h);

                    gl.viewport(0, 0, h, h);
                    gl.draw_full("em_radial", params0);
                    gl.viewport(width - h, 0, h, h);
                    gl.draw_full("em_radial", params1);

                    if (mode === "em5")
                        ctx.globalAlpha = 0.7;

                    ctx.drawImage(gl.finish(), 0, 0, width, h);

                    ctx.globalAlpha = 1;
                }




                ctx.fillStyle = "rgba(180, 180, 180, 0.8)";

                ctx.strokeStyle = "#222";
                for (let i = 0; i < draggables.length; i++) {
                    let d = draggables[i];

                    let r = width * 0.025;

                    if (mode === "em1") {

                        let l = 1.0 - saturate(3.0 * sin(tt * 0.25 - 1));

                        ctx.fillStyle = rgba_color_string([l, l, l, 1]);

                        ctx.fillEllipse(width * d.pos[0], width * d.pos[1], r);
                        ctx.strokeEllipse(width * d.pos[0], width * d.pos[1], r);
                    } else {

                        let n = 34;
                        ctx.save();
                        ctx.translate(width * d.pos[0], width * d.pos[1]);
                        ctx.beginPath();

                        ctx.rect(-2 * r, -2 * r, 4 * r, 4 * r);
                        ctx.clip();
                        ctx.beginPath();

                        for (let k = 0; k < n; k++) {
                            let a = 2 * pi * k / n;
                            let rr = r * (0.9 + 0.3 * hash(k + i * 100));
                            ctx.lineTo(cos(a) * rr, sin(a) * rr);
                        }

                        ctx.closePath();

                        ctx.shadowColor = "rgba(0,0,0,1)";
                        ctx.shadowBlur = 10;
                        ctx.shadowOffsetY = 0;
                        ctx.shadowOffsetX = 0;

                        ctx.fill("evenodd");

                        ctx.save();
                        ctx.clip();

                        ctx.rect(-3 * r, -3 * r, 6 * r, 6 * r);

                        ctx.shadowColor = "rgba(255,255,255,0.1)";
                        ctx.shadowBlur = 0;
                        ctx.shadowOffsetY = r * 0.5 * scale;
                        ctx.shadowOffsetX = 0;

                        ctx.fill("evenodd");

                        ctx.shadowOffsetY = -r * 0.5 * scale;
                        ctx.fill("evenodd");

                        ctx.shadowColor = "rgba(0, 0, 0,0.1)";

                        ctx.shadowOffsetY = 0;
                        ctx.shadowOffsetX = -r * 0.5 * scale;
                        ctx.fill("evenodd");

                        ctx.shadowOffsetX = r * 0.5 * scale;
                        ctx.fill("evenodd");

                        ctx.shadowOffsetX = 0;

                        ctx.restore();


                        ctx.stroke();

                        ctx.restore();
                    }
                }

                if (mode === "em5") {

                    let t = slider_args[1];

                    ctx.save();

                    ctx.beginPath();
                    ctx.rect(0, 0, height, height);
                    ctx.clip();
                    ctx.translate(h / 2, h / 2);
                    ctx.scale(h * 0.5, h * 0.5);

                    ctx.lineWidth = 0.01;



                    let l = total_l * t;

                    let len_cap0 = clamp(l, 0, cap);

                    let len_i0 = clamp(l - cap, 0, li0);
                    let len_i1 = clamp(l - cap, 0, li1);

                    let len_mid0 = clamp(l - cap - (li0), 0, mid_l);
                    let len_mid1 = clamp(l - cap - (li1), 0, mid_l);

                    let len_o0 = clamp(l - cap - (li0) - mid_l, 0, lo0);
                    let len_o1 = clamp(l - cap - (li1) - mid_l, 0, lo1);

                    let len_cap10 = max(l - cap - (li0) - mid_l - lo0, 0);
                    let len_cap11 = max(l - cap - (li1) - mid_l - lo1, 0);



                    {
                        ctx.beginPath();

                        ctx.lineTo(p0x + si * (li0 + 2.2), -p0y - ci * (li0 + 2.2));
                        ctx.lineTo(p0x + si * (li0 + cap - len_cap0), -p0y - ci * (li0 + cap - len_cap0),
                        );

                        if (len_i0 > 0)
                            ctx.lineTo(p0x + si * (li0 - len_i0), -p0y - ci * (li0 - len_i0));


                        if (len_mid0 > 0)
                            ctx.lineTo(lerp(p0x, p1x, len_mid0 / mid_l), -lerp(p0y, p1y, len_mid0 / mid_l));

                        if (len_o0 > 0)
                            ctx.lineTo(p1x + len_o0, -p1y);

                        if (len_cap10 > 0)
                            ctx.lineTo(p1x + len_o0 + len_cap10, -p1y);
                    }

                    ctx.globalAlpha = 0.5;
                    ctx.lineWidth = 0.065;
                    ctx.strokeStyle = "#000";

                    ctx.stroke();

                    ctx.globalAlpha = 0.9;
                    ctx.lineWidth = 0.05;
                    ctx.strokeStyle = color5;
                    ctx.stroke();


                    {

                        ctx.beginPath();

                        ctx.lineTo(p1x + si * (li1 + 2.2), -p1y - ci * (li1 + 2.2));
                        ctx.lineTo(p1x + si * (li1 + cap - len_cap0), -p1y - ci * (li1 + cap - len_cap0));


                        if (len_i1 > 0)
                            ctx.lineTo(p1x + si * (li1 - len_i1), -p1y - ci * (li1 - len_i1));

                        if (len_mid1 > 0)
                            ctx.lineTo(lerp(p1x, p0x, len_mid1 / mid_l), -lerp(p1y, p0y, len_mid1 / mid_l));

                        if (len_o1 > 0)
                            ctx.lineTo(p0x + len_o1, -p0y);

                        if (len_cap11 > 0)

                            ctx.lineTo(p0x + len_o1 + len_cap11, -p0y);


                        ctx.globalAlpha = 0.5;
                        ctx.lineWidth = 0.035;
                        ctx.strokeStyle = "#333";

                        ctx.stroke();

                        ctx.globalAlpha = 0.9;
                        ctx.lineWidth = 0.02;
                        ctx.strokeStyle = color4;
                        ctx.stroke();

                    }


                    ctx.restore();


                    ctx.save();

                    ctx.beginPath();
                    ctx.rect(width - height, 0, height, height);
                    ctx.clip();
                    ctx.translate(h / 2, h / 2);
                    ctx.scale(h * 0.5, h * 0.5);


                    ctx.strokeStyle = color5;
                    ctx.lineWidth = 0.04;

                    ctx.strokeLine(p1x + len_o0, -p1y, p1x + len_o0 + len_cap10, -p1y);

                    ctx.stroke();

                    ctx.strokeStyle = color4;
                    ctx.lineWidth = 0.02;

                    ctx.strokeLine(p0x + len_o1, -p0y, p0x + len_o1 + len_cap11, -p0y);

                    ctx.restore();
                }

                ctx.feather(height * scale, height * scale,
                    canvas.height * 0.1, canvas.height * 0.1,
                    canvas.height * 0.1, canvas.height * 0.1);


                ctx.feather(height * scale, height * scale,
                    canvas.height * 0.1, canvas.height * 0.1,
                    canvas.height * 0.1, canvas.height * 0.1, (width - height) * scale, 0);

                let s = width * 0.04;
                ctx.strokeStyle = "#000";
                if (mode != "em1") {
                    ctx.save();

                    ctx.translate(height / 2, height / 2);

                    ctx.rotate(a - pi / 2);
                    ctx.fillStyle = color0;



                    ctx.arrow(height * 0.45, 0, height * 0.45 - 1.5 * s, 0, s * 0.2, s * 0.55, s * 0.7);

                    ctx.fill();
                    ctx.stroke();
                    ctx.restore();
                }


                ctx.save();

                ctx.translate(width - height / 2, height / 2);

                ctx.fillStyle = color2;

                ctx.arrow(-0.5 * s, 0, -2 * s, 0, s * 0.2, s * 0.55, s * 0.7);

                ctx.fill();
                ctx.stroke();

                ctx.fillStyle = color1;

                ctx.strokeStyle = "#000";
                ctx.fillEllipse(0, 0, s * 0.2);
                ctx.strokeEllipse(0, 0, s * 0.2);


                ctx.restore();



                ctx.save();

                ctx.strokeStyle = "#444";
                ctx.translate(width / 2, height / 2);

                ctx.arrow(-s * 0.75, 0, s * 0.75, 0, s * 0.2, s * 0.55, s * 0.7);

                ctx.stroke();

                ctx.fillStyle = "#444";

                ctx.fillText("far", 0, -font_size * 0.8);
                ctx.fillText("away", 0, font_size * 1.3);

                ctx.restore();


                if (mode !== "em5") {
                    ctx.resetTransform();
                    ctx.save();
                    ctx.fillStyle = "#000";
                    ctx.shadowColor = "rgba(0,0,0,1.0)";
                    ctx.shadowBlur = canvas.width * 0.05 * 0.5;
                    ctx.shadowOffsetY = -55 * scale;
                    ctx.shadowOffsetX = 55 * scale;
                    ctx.globalCompositeOperation = "destination-out";
                    ctx.fillRect(-200, height * scale, 200, 200);
                    ctx.restore();
                }

            }


            /* Helpers */


            function SPHSim(capacity) {
                let _pos = new Float64Array(capacity * 2);
                let _vel = new Float64Array(capacity * 2);
                let _pres = new Float64Array(capacity);
                let _rho = new Float64Array(capacity);

                let _acc = new Float64Array(capacity * 2);
                let _drho = new Float64Array(capacity * 2);

                let _n = 0;

                let _tree = new Int16Array(capacity * 8);
                let _tree_vals = new Float64Array(capacity * 4 * 3);
                let _tree_stack = new Int32Array(capacity * 8);

                this._min_x = +Infinity;
                this._max_x = -Infinity;
                this._min_y = +Infinity;
                this._max_y = -Infinity;

                this._tree = _tree;

                this.set_initial_values = function (positions, velocities, heavy_n) {

                    if (positions) {
                        _n = positions.length;

                        for (let i = 0; i < _n; i += 2) {
                            _pos[i] = positions[i];
                            _pos[i + 1] = positions[i + 1];

                            this._min_x = min(this._min_x, _pos[i]);
                            this._max_x = max(this._max_x, _pos[i]);
                            this._min_y = min(this._min_y, _pos[i + 1]);
                            this._max_y = max(this._max_y, _pos[i + 1]);
                        }

                        if (velocities) {
                            for (let i = 0; i < _n; i++)
                                _vel[i] = velocities[i];
                        }

                        _n /= 2;
                    }

                    for (let i0 = 0; i0 < _n; i0++) {
                        let m0 = i0 < heavy_n ? _heavy_mass : _base_mass;
                        _drho[i0] = m0 * kernel_k;
                        _rho[i0] = m0 * kernel_k;
                    }

                    this.positions = _pos;
                    this.velocities = _vel;
                    this.n = _n;

                    _heavy_n = heavy_n;

                }

                const spacing = 1;
                const _base_rho = 2.5e3;
                const _base_mass = spacing * spacing * spacing * _base_rho;
                const _heavy_mass = 1.6 * _base_mass;

                const _bulk_modulus = 8e6;
                const _speed_of_sound = _bulk_modulus / _base_rho;

                let _heavy_n;


                const kernel_k = 40.0 / (7.0 * pi);



                let prev_tvx = 0;
                let prev_tvy = 0;


                this.step = function () {

                    const pos = _pos;
                    const vel = _vel;
                    const pres = _pres;
                    const rho = _rho;
                    const acc = _acc;
                    const drho = _drho;

                    const base_mass = _base_mass;
                    const heavy_mass = _heavy_mass;

                    const bulk_modulus = _bulk_modulus;
                    const speed_of_sound = _speed_of_sound;
                    const base_rho = _base_rho;

                    const n = _n;
                    const heavy_n = _heavy_n;

                    const kernel_k = 40.0 / (7.0 * pi);

                    const quality_factor = 2.5;

                    const dt = 0.00035;

                    let min_x = this._min_x;
                    let max_x = this._max_x;
                    let min_y = this._min_y;
                    let max_y = this._max_y;


                    /* Build Barnes-Hut tree */

                    const empty_tree_marker = 0;

                    const tree = _tree;
                    const tree_vals = _tree_vals;
                    const tree_stack = _tree_stack;

                    tree[0] = empty_tree_marker;
                    tree[1] = empty_tree_marker;
                    tree[2] = empty_tree_marker;
                    tree[3] = empty_tree_marker;
                    tree_vals[0] = 0;
                    tree_vals[1] = 0;
                    tree_vals[2] = 0;

                    let next_tree_i = 4;

                    const OOB_limit = 500;

                    /* Just skip the first particle, empty tree marker is 0. */

                    for (let i0 = 1; i0 < n; i0++) {

                        let p0x = pos[i0 * 2];
                        let p0y = pos[i0 * 2 + 1];

                        if (abs(p0y) > OOB_limit || abs(p0x) > OOB_limit)
                            continue;

                        let m0 = i0 < heavy_n ? heavy_mass : base_mass;

                        let tree_i = 0;

                        let local_min_x = min_x;
                        let local_max_x = max_x;
                        let local_min_y = min_y;
                        let local_max_y = max_y;

                        let mid_local_x = 0.5 * (local_min_x + local_max_x);
                        let mid_local_y = 0.5 * (local_min_y + local_max_y);

                        let depth = 128;

                        while (depth-- > 0) {

                            tree_vals[tree_i * 3 + 0] += m0 * p0x;
                            tree_vals[tree_i * 3 + 1] += m0 * p0y;
                            tree_vals[tree_i * 3 + 2] += m0;

                            if (p0x > mid_local_x) {
                                local_min_x = mid_local_x;
                                tree_i += 1;
                            } else {
                                local_max_x = mid_local_x;
                            }

                            if (p0y > mid_local_y) {
                                local_min_y = mid_local_y;
                                tree_i += 2;
                            } else {
                                local_max_y = mid_local_y;
                            }

                            let existing_tree_value = tree[tree_i];

                            if (existing_tree_value == empty_tree_marker) {
                                tree[tree_i] = i0;
                                break;
                            }


                            mid_local_x = 0.5 * (local_min_x + local_max_x)
                            mid_local_y = 0.5 * (local_min_y + local_max_y)


                            if (existing_tree_value >= 0) {
                                /* Split */

                                let i1 = existing_tree_value;

                                /* Link new subtrees */

                                tree[tree_i] = -next_tree_i;

                                tree.fill(empty_tree_marker, next_tree_i, next_tree_i + 4);
                                tree_vals.fill(0, next_tree_i * 3, next_tree_i * 3 + 12);

                                /* Move existing particle to new subtree */

                                let p1x = pos[i1 * 2];
                                let p1y = pos[i1 * 2 + 1];
                                let m1 = i1 < heavy_n ? heavy_mass : base_mass;

                                let ix = p1x > mid_local_x ? 1 : 0;
                                let iy = p1y > mid_local_y ? 2 : 0;

                                let new_tree_i = next_tree_i + ix + iy;

                                tree[new_tree_i] = i1;

                                tree_vals[next_tree_i * 3 + 0] += m1 * p1x;
                                tree_vals[next_tree_i * 3 + 1] += m1 * p1y;
                                tree_vals[next_tree_i * 3 + 2] += m1;

                                tree_i = next_tree_i;
                                next_tree_i += 4;

                            } else {
                                tree_i = -existing_tree_value;
                            }
                        }
                    }


                    let kk = next_tree_i * 3;

                    for (let i = 0; i < kk; i += 3) {
                        let inv_tree_m = 1 / tree_vals[i + 2];
                        tree_vals[i + 0] *= inv_tree_m;
                        tree_vals[i + 1] *= inv_tree_m;
                    }

                    const g = 0.5;

                    const size_scale = (1 << 28);

                    let w = max_x - min_x;
                    let h = max_y - min_y;
                    let max_size = max(w, h);
                    max_size = max_size * max_size * quality_factor;

                    max_size /= size_scale;

                    min_x = +Infinity;
                    max_x = -Infinity;
                    min_y = +Infinity;
                    max_y = -Infinity;

                    let tvx = 0;
                    let tvy = 0;


                    for (let i0 = 1; i0 < n; i0++) {

                        let p0x = pos[i0 * 2];
                        let p0y = pos[i0 * 2 + 1];

                        if (abs(p0y) > OOB_limit || abs(p0x) > OOB_limit)
                            continue;

                        let m0 = i0 < heavy_n ? heavy_mass : base_mass;

                        let rho0 = rho[i0];
                        let p0_over_rho0_sq = pres[i0];

                        let v0x = vel[i0 * 2];
                        let v0y = vel[i0 * 2 + 1];

                        let a0x = acc[i0 * 2];
                        let a0y = acc[i0 * 2 + 1];

                        let new_rho0 = drho[i0] + m0 * kernel_k;

                        let stack_count = 0;
                        let stack_index = 0;

                        for (let i = 0; i < 4; i++) {
                            if (tree[i] != 0) {
                                tree_stack[stack_count++] = tree[i];
                                tree_stack[stack_count++] = size_scale;
                            }
                        }

                        while (stack_index < stack_count) {
                            let value = tree_stack[stack_index + 0];
                            let scale = tree_stack[stack_index + 1];

                            if (value > 0) {

                                /* Leaf node. */

                                let i1 = value;
                                let m1 = i1 < heavy_n ? heavy_mass : base_mass;

                                let dx = p0x - pos[i1 * 2];
                                let dy = p0y - pos[i1 * 2 + 1];
                                let r2 = dx * dx + dy * dy;

                                let r = sqrt(r2);
                                let fg = -g / (r2 * r + 0.01);

                                a0x += m1 * dx * fg;
                                a0y += m1 * dy * fg;


                                let a1x = -dx * fg;
                                let a1y = -dy * fg;

                                /* Base SPH */

                                if (r < 1) {

                                    let p1_over_rho1_sq = pres[i1];

                                    let v1x = vel[i1 * 2];
                                    let v1y = vel[i1 * 2 + 1];
                                    let rho1 = rho[i1];

                                    let dvx = v0x - v1x;
                                    let dvy = v0y - v1y;

                                    let nr = 1.0 - r;

                                    let grad_factor = 0;
                                    let factor = 0;

                                    if (r <= 0.5) {
                                        factor = (-6.0 * r2 * nr + 1.0);
                                        grad_factor = r * (18.0 * r - 12.0);
                                    } else {
                                        let nr2 = nr * nr;
                                        factor = 2.0 * nr * nr2;
                                        grad_factor = -6.0 * nr2;
                                    }

                                    let inv_r = 1.0 / (r + 0.001);

                                    grad_factor *= kernel_k * inv_r;

                                    let p = -(p0_over_rho0_sq + p1_over_rho1_sq);

                                    const alpha = 1.0 * 0.1;
                                    const beta = 2.0 * 0.1;

                                    let vr = dx * dvx + dy * dvy;

                                    let pij = 0.0;

                                    if (vr < 0.0) {
                                        let mu = vr * inv_r * inv_r;

                                        let rhobar = 0.5 * (rho0 + rho1);
                                        let csbar = speed_of_sound;
                                        pij = (beta * mu - alpha * csbar) * mu / rhobar;
                                    }

                                    let da = (p - pij) * grad_factor;

                                    let gradx = dx * da;
                                    let grady = dy * da;

                                    a0x += m1 * gradx;
                                    a0y += m1 * grady;

                                    new_rho0 += factor * m1;

                                    a1x -= gradx;
                                    a1y -= grady;

                                    drho[i1] += factor * m0;
                                }

                                acc[i1 * 2] += a1x * m0;
                                acc[i1 * 2 + 1] += a1y * m0;

                                stack_index += 2;
                                continue;
                            }

                            let tree_i = -value;

                            let tree_x = tree_vals[tree_i * 3 + 0];
                            let tree_y = tree_vals[tree_i * 3 + 1];

                            let dx = p0x - tree_x;
                            let dy = p0y - tree_y;
                            let r2 = dx * dx + dy * dy;

                            if (r2 > max(2, max_size * scale)) {
                                let tree_m = tree_vals[tree_i * 3 + 2];

                                let r = sqrt(r2);
                                let fg = -g / (r2 * r + 0.01);
                                a0x += tree_m * dx * fg;
                                a0y += tree_m * dy * fg;

                                stack_index += 2;
                                continue;
                            }

                            /* Barnes-Hut tree traversal */

                            let next_tree_value0 = tree[tree_i + 0];
                            let next_tree_value1 = tree[tree_i + 1];
                            let next_tree_value2 = tree[tree_i + 2];
                            let next_tree_value3 = tree[tree_i + 3];

                            scale >>= 2;

                            if (next_tree_value0 < 0 || next_tree_value0 > i0) {
                                tree_stack[stack_count + 0] = next_tree_value0;
                                tree_stack[stack_count + 1] = scale;
                                stack_count += 2;
                            }

                            if (next_tree_value1 < 0 || next_tree_value1 > i0) {
                                tree_stack[stack_count + 0] = next_tree_value1;
                                tree_stack[stack_count + 1] = scale;
                                stack_count += 2;
                            }

                            if (next_tree_value2 < 0 || next_tree_value2 > i0) {
                                tree_stack[stack_count + 0] = next_tree_value2;
                                tree_stack[stack_count + 1] = scale;
                                stack_count += 2;
                            }

                            if (next_tree_value3 < 0 || next_tree_value3 > i0) {
                                tree_stack[stack_count + 0] = next_tree_value3;
                                tree_stack[stack_count + 1] = scale;
                                stack_count += 2;
                            }

                            stack_index += 2;
                        }


                        v0x += a0x * dt - prev_tvx;
                        v0y += a0y * dt - prev_tvy;

                        new_rho0 *= kernel_k;

                        tvx += v0x;
                        tvy += v0y;

                        vel[i0 * 2] = v0x;
                        vel[i0 * 2 + 1] = v0y;
                        rho[i0] = new_rho0;

                        p0x += v0x * dt;
                        p0y += v0y * dt;

                        min_x = min(min_x, p0x);
                        max_x = max(max_x, p0x);
                        min_y = min(min_y, p0y);
                        max_y = max(max_y, p0y);


                        pos[i0 * 2] = p0x;
                        pos[i0 * 2 + 1] = p0y;

                        /* Update pressure */

                        let eta_limit = 0.9;

                        let eta = new_rho0 / base_rho;

                        eta *= base_mass / m0;

                        let eta2 = eta * eta;

                        let p0 = 0.0;
                        let p1 = bulk_modulus / 4.0 * (eta2 * eta2 - 1.0);
                        let p = eta < eta_limit ? p0 : p1;

                        pres[i0] = p / (new_rho0 * new_rho0);
                    }

                    /* Cleanup for next iteration */

                    acc.fill(0, 0, n * 2);
                    drho.fill(0, 0, n);

                    if (n) {
                        prev_tvx = tvx / n;
                        prev_tvy = tvy / n;
                    }

                    this._min_x = min_x;
                    this._max_x = max_x;
                    this._min_y = min_y;
                    this._max_y = max_y;

                    let stats = new Array();
                    for (let i0 = 1; i0 < n; i0++) {

                        let p0x = pos[i0 * 2];
                        let p0y = pos[i0 * 2 + 1];
                        stats.push(sqrt(p0x * p0x + p0y * p0y));

                    }

                    stats;
                }
            }

            function draw_date_and_time(x, y, t, colored, dim = true) {
                ctx.save();
                ctx.fillStyle = "white";

                let a = jd_to_time(t);
                let date = new Date(Date.UTC(a.year, a.month - 1, a.day, a.hour, a.minute));
                let date_options = {
                    year: "numeric",
                    month: "2-digit",
                    day: "2-digit",

                };

                let time_options = {
                    hour: "2-digit",
                    minute: "2-digit",
                };

                let date_str = date.toLocaleString(undefined, date_options);

                let time_str = date.toLocaleString(undefined, time_options);

                ctx.font = round((colored ? 0.8 : 0.75) * font_size) + "px IBM Plex Sans";

                ctx.textAlign = "right";

                ctx.shadowColor = "rgba(0,0,0,1)";
                ctx.shadowBlur = 20;
                ctx.shadowOffsetY = 0;
                ctx.shadowOffsetX = 0;
                ctx.fillStyle = "rgba(0,0,0,0.9)";
                ctx.fillText(date_str, x, y + font_size * 0.8);
                ctx.fillText(time_str, x, y + font_size * 1.8);

                ctx.shadowBlur = 6;
                ctx.fillText(date_str, x, y + font_size * 0.8);
                ctx.fillText(time_str, x, y + font_size * 1.8);

                let c = dim ? "#444" : "#999";
                ctx.shadowColor = "rgba(0,0,0,1)";
                ctx.shadowBlur = 3;
                ctx.fillStyle = colored ? color_date : c;
                ctx.fillText(date_str, x, y + font_size * 0.8);
                ctx.fillStyle = colored ? color_time : c;
                ctx.fillText(time_str, x, y + font_size * 1.8);

                ctx.restore();
            }

            function draw_barycenter(x, y, size) {
                ctx.fillStyle = "#ddd";
                ctx.fillEllipse(x, y, size);
                ctx.fillStyle = "#000";
                ctx.fillEllipse(x, y, size * 0.7);
                ctx.fillStyle = "#ddd";
                ctx.fillEllipse(x, y, size * 0.3);
            }

            function pretty_distance(km) {
                if (metric)
                    return comma_number(round(km)) + " km";
                else
                    return comma_number(round(km / 1.609)) + " mi";
            }

            function pretty_angle(a) {
                return (a * 180 / pi).toFixed(2) + "°";
            }

            function comma_number(n) {
                if (n === 0)
                    return "0";

                let str = "";
                let comma = false;
                while (n > 0) {
                    let k = floor(n / 1000) * 1000;
                    let s = n - k;
                    str = s + (comma ? "," : "") + str;
                    n = k / 1000;
                    if (n > 0) {
                        if (s < 10)
                            str = "00" + str;
                        else if (s < 100)
                            str = "0" + str;
                    }

                    comma = true;
                }
                return str;
            }

            function sphere_limiter(p) {

                let ll = 0.45;
                p = vec_sub(p, [0.5, 0.5]);
                let l = max(ll, vec_len(p));
                p = vec_scale(p, ll / l);

                p = vec_add(p, [0.5, 0.5]);
                return p;
            }

            function world_to_drag_sphere(lat, lon, r, mat) {
                let pos = [r * cos(lat) * cos(lon), r * cos(lat) * sin(lon), r * sin(lat)];

                pos = mat4_mul_vec3(mat, pos);
                pos = vec_scale(pos, 1 / pos[3])

                pos[0] = (pos[0] * 0.5 + 0.5);
                pos[1] = (-pos[1] * 0.5 + 0.5);

                return pos.slice(0, 2);
            }



            function drag_to_world_sphere(p, rr, ivp) {


                let pp0 = [0, 0, 0, 1];
                pp0[0] = p[0] * 2 - 1;
                pp0[1] = -p[1] * 2 + 1;
                pp0[2] = -1;

                let pp1 = pp0.slice();
                pp1[2] = 0;

                pp0 = mat4_mul_vec4(ivp, pp0);
                pp0 = vec_scale(pp0, 1 / pp0[3]);

                pp1 = mat4_mul_vec4(ivp, pp1);
                pp1 = vec_scale(pp1, 1 / pp1[3]);

                let ray_org = pp0.slice(0, 3);
                let ray_dir = vec_norm(vec_sub(pp1.slice(0, 3), pp0.slice(0, 3)));
                let sr = rr;
                let tr = [0, 0, 0];

                let oc = vec_sub(ray_org, tr);
                let b = vec_dot(oc, ray_dir);
                let c = vec_dot(oc, oc) - sr * sr;
                let h = b * b - c;


                let t = -b - Math.sqrt(Math.max(0, h));
                let hit = vec_add(ray_org, vec_scale(ray_dir, t));

                hit = vec_norm(hit);

                let lat = asin(hit[2]);
                let lon = atan2(hit[1], hit[0]);
                return [lat, lon];
            }


            function transmittance_color(dir, sun) {

                if (dir[2] < 0)
                    return [1, 1, 1, 1];

                function quick_sphere(ray_org, ray_dir, r2) {
                    let oc = ray_org;
                    let b = vec_dot(oc, ray_dir);
                    let c = vec_dot(oc, oc) - r2;
                    let h = b * b - c;

                    if (h < 0.0) return RAY_MAX;

                    return -b + sqrt(h);
                }


                const rS = [0.005802, 0.013558, 0.033100];

                const mS = 0.001;
                const mA = 0.004440;

                const oA = [0.000650, 0.001881, 0.000085];

                const r0 = 6371.0;
                const r1 = 6451.0;

                let pos = [0, 0, r0];

                let dist = quick_sphere(pos, dir, r1 * r1);

                const steps = 40.0;
                let step = dist / steps;

                let optical_depth = [0, 0, 0];

                for (let i = 0; i < steps; i++) {

                    let altitude = vec_len(pos) - r0;

                    let rD = exp(-altitude / 8.0);
                    let mD = exp(-altitude / 1.2);
                    let oD = max(0.0, 1.0 - abs(altitude - 25.0) / 15.0);

                    optical_depth = vec_add(optical_depth, vec_scale(rS, rD));
                    optical_depth = vec_add(optical_depth, vec_scale([1, 1, 1], (mS + mA) * mD));
                    optical_depth = vec_add(optical_depth, vec_scale(oA, oD));;

                    pos = vec_add(pos, vec_scale(dir, step));
                }

                let c = [0, 0, 0, 1];

                if (sun) {

                    const map_min = -11.5;
                    const map_max = -1.;

                    for (let i = 0; i < 3; i++) {
                        let v = exp(-step * optical_depth[i]);

                        v *= 4;

                        v = clamp(Math.log2(v), map_min, map_max);
                        v = (v - map_min) / (map_max - map_min);

                        v = (((((15.5 * v - 40.14) * v + 31.96) * v - 6.868) * v + 0.4298) * v + 0.1191) * v - 0.00232;

                        c[i] = saturate(v);
                    }
                } else {

                    let m = 0.0;

                    for (let i = 0; i < 3; i++) {
                        let v = exp(-step * optical_depth[i]);
                        c[i] = v;
                        m = max(m, v);
                    }

                    for (let i = 0; i < 3; i++) {

                        let v = c[i];
                        v /= m;
                        v = linear_to_srgb(v);

                        v = v * 0.7 + 0.3;

                        c[i] = saturate(v);
                    }

                }


                return c;
            }

            function eccentric_anomaly(e, M) {
                function f(E) {
                    return E - e * Math.sin(E) - M;
                }

                function fp(E) {
                    return 1 - e * Math.cos(E);
                }

                let E = M;
                let old_E;
                for (let i = 0; i < 20; i++) {
                    old_E = E;
                    E = E - f(E) / fp(E);
                    if (Math.abs(old_E - E) < 0.00000001)
                        break;
                }

                return E;
            }

            function true_anomaly(e, E) {
                return 2 * Math.atan(Math.sqrt((1 + e) / (1 - e)) * Math.tan(E * 0.5));
            }

            function project(p) {
                p = vec_scale(p, 1 / p[3]);
                p[0] *= width * 0.5;
                p[1] *= -height * 0.5;
                return p;
            }

            function sphere_gradient(x, y, r, base_color) {
                let grad = ctx.createRadialGradient(x, y, 0, x, y, r);

                for (let i = 0; i <= 32; i++) {
                    let t = i / 32;
                    let s = cos(t * pi * 0.5);

                    s = lerp(s, 1, 0.05);
                    s = linear_to_srgb(s);

                    grad.addColorStop(t, rgba_color_string(vec_mul(base_color, [s, s, s, 1])));
                }
                return grad;
            }


            function int(a) {
                return a < 0 ? Math.ceil(a) : Math.floor(a);
            }

            function jd_to_time(t) {
                t += 0.5;
                let Z = int(t);
                let F = t - Z;
                let alpha = floor((Z - 1867216.25) / 36524.25);
                let A = Z + 1 + alpha - int(alpha * 0.25);
                let B = A + 1524;
                let C = int((B - 122.1) / 365.25);
                let D = int(365.25 * C);
                let E = int((B - D) / 30.6001);

                let day = B - D - int(30.6001 * E) + F;
                let month = E - (E < 14 ? 1 : 13);
                let year = C - (month > 2 ? 4716 : 4715);

                let H = 24 * (day - int(day));
                let hour = floor(H);
                let minute = 60 * (H - hour);
                let second = 60 * (minute - floor(minute));
                if (second > 59.5)
                    minute = ceil(minute);

                return { year, month, day: int(day), hour, minute };
            }

            function JD(y, m, d) {


                if (m == 1 || m == 2) {
                    y--;
                    m += 12;
                }

                let a = int(y / 100);
                let b = 2 - a + int(a / 4);
                return int(365.25 * (y + 4716)) + int(30.6 * (m + 1)) + d + b - 1524.5;
            }


            function bisect(a, b, f) {
                let fa = f(a);

                for (let i = 0; i < 30; i++) {
                    let mid = (a + b) / 2;
                    let fmid = f(mid);

                    if (Math.abs(fmid) < 0.000001)
                        return mid;

                    if ((fmid > 0 && fa > 0) || (fmid < 0 && fa < 0)) {
                        a = mid;
                        fa = f(a);
                    } else {
                        b = mid;
                    }
                }

                return a;
            }

            function linear_to_srgb(c) {
                return c < 0.0031308 ? 12.92 * c : 1.055 * pow(c, 1.0 / 2.4) - 0.055;
            }

            function draw_figurine(gl, mat, rot, arm_a, head_a, shaded = true) {

                let c = rgba_hex_color(0xDF1E1E, 1.0);
                c[3] = shaded ? 1 : 0;

                let leg0 = translation_mat4([1., 0, -0.5]);
                leg0 = mat4_mul(mat, leg0);
                gl.draw_simple("parted_sphere", leg0, rot, { color: c, spread: [0, 0, 3] });

                let leg1 = translation_mat4([-1., 0, -0.5]);
                leg1 = mat4_mul(mat, leg1);
                gl.draw_simple("parted_sphere", leg1, rot, { color: c, spread: [0, 0, 3] });

                let torso = translation_mat4([0, 0, 4]);
                torso = mat4_mul(mat, torso);
                gl.draw_simple("parted_sphere", torso, rot, { color: c, spread: [1.0, 0., 2] });

                let shoulders = scale_mat4(0.8);
                shoulders = mat4_mul(translation_mat4([0, 0, 6.1]), shoulders);
                shoulders = mat4_mul(mat, shoulders);
                gl.draw_simple("parted_sphere", shoulders, rot, { color: c, spread: [2.4, 0., 0] });


                let arm0 = translation_mat4([0, 0, -3.2]);
                arm0 = mat4_mul(rot_y_mat4(-0.05), arm0);
                arm0 = mat4_mul(rot_x_mat4(arm_a), arm0);
                arm0 = mat4_mul(scale_mat4(0.7), arm0);
                arm0 = mat4_mul(translation_mat4([2.6, 0, 6.1]), arm0);
                arm0 = mat4_mul(mat, arm0);
                gl.draw_simple("parted_sphere", arm0, mat3_mul(rot, rot_x_mat3(arm_a)), { color: c, spread: [0, 0, 3.4] });


                let arm1 = translation_mat4([0, 0, -3.2]);
                arm1 = mat4_mul(rot_y_mat4(0.05), arm1);

                arm1 = mat4_mul(scale_mat4(0.7), arm1);
                arm1 = mat4_mul(translation_mat4([-2.6, 0, 6.1]), arm1);
                arm1 = mat4_mul(mat, arm1);
                gl.draw_simple("parted_sphere", arm1, rot, { color: c, spread: [0, 0, 3.4] });


                let head = translation_mat4([0, 0, -0.2]);
                head = mat4_mul(rot_x_mat4(head_a), head);
                head = mat4_mul(scale_mat4(1.4), head);
                head = mat4_mul(translation_mat4([0, 0.2, 8.3]), head);
                head = mat4_mul(mat, head);
                gl.draw_simple("parted_sphere", head, mat3_mul(rot, rot_x_mat3(head_a)), { color: c, spread: [0, 0, 0.2] });

            }

            function lambert_radiance(light, view, norm) {
                return saturate(vec_dot(light, norm)) * 0.4 / pi;
            }

            function hapke_radiance(light, view, norm) {

                let b = 0.23;
                let c = 0.6;
                let hs = 0.06;
                let Bs0 = 1.8;
                let w = 0.4;
                let K = 1.0;

                let cosi = saturate(vec_dot(light, norm));
                let cose = saturate(-vec_dot(view, norm));

                if (cosi <= 0)
                    return 0;

                let cosg = saturate(-vec_dot(view, light));
                let sing = sqrt(1.0 - cosg * cosg);
                let tang2 = (1.0 - cosg) / (sing + 0.00001);

                let LS = cosi / (cosi + cose);

                let b2 = b * b;
                let pdenom0 = 1.0 - 2.0 * b * cosg + b2;
                let pdenom1 = 1.0 + 2.0 * b * cosg + b2;
                let p = (0.5 + 0.5 * c) * (1.0 - b2) / (pdenom0 * sqrt(pdenom0)) +
                    (0.5 - 0.5 * c) * (1.0 - b2) / (pdenom1 * sqrt(pdenom1));

                let Bs = 1.0 / (1.0 + tang2 / hs);

                let gamma = sqrt(1.0 - w);

                let Hi = (1.0 + 2.0 * cosi / K) / (1.0 + 2.0 * gamma * cosi / K);
                let He = (1.0 + 2.0 * cose / K) / (1.0 + 2.0 * gamma * cose / K);

                let M = Hi * He - 1.0;

                return LS * K * w * 0.25 * (p * (1.0 + Bs0 * Bs) + M) * 0.4 / 0.629197;
            }


            function draw_moon_phase_label(m_pos, e_pos, ecliptic_p_z) {

                function project(vec) {
                    return vec_sub(vec, vec_scale(ecliptic_p_z, vec_dot(vec, ecliptic_p_z)));
                }
                let d0 = vec_norm(project(vec_sub(m_pos, e_pos)));
                let d1 = vec_norm(project(vec_neg(m_pos)));

                let a = acos(vec_dot(d0, d1));

                if (vec_cross(d0, d1)[2] < 0)
                    a = -a;

                a = -a;

                let ranges = [
                    [-200, "full moon"],
                    [-173, "waning gibbous"],
                    [-97, "last quarter"],
                    [-83, "waning crescent"],
                    [-7, "new moon"],
                    [7, "waxing crescent"],
                    [83, "first quarter"],
                    [97, "waxing gibbous"],
                    [173, "full moon"],
                    [200, "full moon"],
                ]

                a *= 180 / pi;

                for (let i = 0; i < ranges.length - 1; i++) {
                    if (a >= ranges[i][0] && a < ranges[i + 1][0]) {

                        let da = 4;
                        let alpha = smooth_step(ranges[i][0], ranges[i][0] + da, a) -
                            smooth_step(ranges[i + 1][0] - da, ranges[i + 1][0], a);
                        ctx.globalAlpha = alpha;
                        ctx.fillText(ranges[i][1], 0, 0);
                        break;
                    }
                }
            }


            self.first_draw = false;
        }

        if (args.animated)
            this.set_paused(false);

        if (args.has_text)
            document.fonts.load("10px IBM Plex Sans").then(function () { request_repaint(true); });

        window.addEventListener("resize", this.on_resize, true);
        window.addEventListener("load", this.on_resize, true);

        this.on_resize();
    }


    document.addEventListener("DOMContentLoaded", function (event) {

        if (!localStorage.getItem("global.metric")) {
            let language = window.navigator.userLanguage || window.navigator.language;
            if (language == "en_US" || language == "en-US") {
                metric = false;
            }
        } else {
            metric = localStorage.getItem("global.metric") === "true";
        }

        if (!metric)
            document.body.classList.add("show_imperial");


        let switches = document.getElementsByClassName("unit_switch");
        for (let sw of switches) {

            let handle = sw.classList.contains("short_time") || sw.classList.contains("long_time") ? switch_time_units : switch_units;
            sw.addEventListener('click', function (event) {
                event.preventDefault();
                handle();
            });
        }


        function make_drawer(name, args = {}, slider_count = 0, slider_values = [0.5, 0.5, 0.5]) {

            let drawer_container = document.getElementById(name);
            let drawer = new Drawer(drawer_container, name, args);
            let sliders = [];

            for (let i = 0; i < slider_count; i++) {
                let slider = new Slider(document.getElementById(name + "_sl" + i), function (x) {
                    drawer.set_slider_arg(i, x, true);
                }, undefined, slider_values[i]);

                sliders.push(slider);
            }

            drawer.set_sliders(sliders, slider_values);

            let d = {};
            d.drawer = drawer;
            d.sliders = sliders;

            drawers_map[name] = d;

            return d;
        }



        make_drawer("table_image0", { two_axis: { vertical_limits: [-pi / 2, -pi / 2], angles: [0, -pi / 2] } });
        make_drawer("table_image1", { two_axis: { vertical_limits: [-pi / 2, -pi / 2], angles: [0, -pi / 2] } }, 1, [0]);


        make_drawer("moon1", { has_arcball: true, needs_eph: true, rotation: mat3_mul(rot_x_mat3(-pi / 2), rot_z_mat3(-pi / 2)) }, 1, [0]);
        make_drawer("moon3", { has_arcball: true, needs_eph: true, rotation: mat3_mul(rot_x_mat3(-1.2), rot_z_mat3(-pi / 2)) }, 1, [0]);
        make_drawer("moon5", { has_arcball: true, has_units: true, rotation: mat3_mul(rot_x_mat3(-1.2), rot_z_mat3(-pi / 2)) });
        make_drawer("moon7", { has_arcball: true, needs_eph: true, rotation: mat3_mul(rot_x_mat3(-1.2), rot_z_mat3(-pi / 2)), has_draggables: true }, 1, [0]);

        make_drawer("eclipse");

        make_drawer("brdf1", { has_arcball: true, rotation: rot_y_mat3(-1.5) }, 1, [0.3]);
        make_drawer("brdf2", { has_arcball: true, rotation: rot_y_mat3(-1.5) }, 1, [0.3]);
        make_drawer("brdf3", { has_arcball: true, rotation: rot_y_mat3(1.7), has_text: true });

        make_drawer("brdf4a", { has_arcball: true, rotation: mat3_mul(rot_x_mat3(-0.8), rot_y_mat3(-1.5)) });
        make_drawer("brdf4", { has_arcball: true, rotation: rot_y_mat3(-1.), companion: drawers_map["brdf4a"].drawer }, 1);

        make_drawer("shadow_hiding", { two_axis: { vertical_limits: [-pi * 0.42, 0], angles: [0.4, -1] }, rotation: ident_mat3 }, 1);

        make_drawer("shadow_hiding2", { two_axis: { vertical_limits: [-pi / 2, 0], angles: [0.4, -1] }, rotation: ident_mat3 }, 1);


        make_drawer("earth_scale", {
            has_text: true, has_units: true
        }, 1, [0]);

        make_drawer("sun_scale", {
            has_text: true, has_units: true
        }, 1, [0]);

        make_drawer("gravity", {
            has_draggables: true, has_text: true, has_units: true
        }, 2, [0.293, 0.697]);

        make_drawer("gravity2", {
            has_draggables: true, has_text: true, has_units: true
        }, 2, [0.293, 0.697]);

        make_drawer("com", {
            has_draggables: true, has_text: true
        }, 2, [0.293, 0.697]);

        make_drawer("fov", {
            has_draggables: true, has_text: true
        }, 1, [0.5]);


        make_drawer("em_mesh", { has_arcball: true, animated: true, rotation: rot_x_mat3(-0.7) }, 1, [0.5]);

        make_drawer("em1", { has_draggables: true, has_text: true, animated: true }, 1, [0.5]);
        make_drawer("em2", { has_draggables: true, has_text: true, animated: true }, 2, [0.5]);

        make_drawer("em3", { has_draggables: true, has_text: true, animated: true }, 2, [0.5]);

        make_drawer("em4", { has_draggables: true, has_text: true, animated: true }, 2, [0.5]);

        make_drawer("em4a", { has_draggables: true, has_text: true, animated: true }, 2, [0.5]);

        em4a_seg = new SegmentedControl(document.getElementById("em4a_seg0"), function (x) {
            em4a.drawer.set_slider_arg(2, x);
        }, ["incoming", "scattered once", "scattered twice"]);


        make_drawer("em5", { has_draggables: true, has_text: true }, 2, [0.5, 0]);

        make_drawer("angular_momentum", { animated: true }, 1);
        make_drawer("twist", {}, 1, [0]);
        make_drawer("shadow", { has_draggables: true, has_text: true });

        make_drawer("ellipse1", { animated: true }, 2);
        make_drawer("ellipse2", { animated: true }, 1, [0]);
        make_drawer("ellipse3", { animated: true }, 1, [0]);

        let space_sim_params = {
            simulated: true, has_reset: true, animated: true, has_draggables: true
        };

        make_drawer("space_sim1", space_sim_params);
        make_drawer("space_sim1a", space_sim_params);
        make_drawer("space_sim2", space_sim_params);
        make_drawer("space_sim3", space_sim_params);
        make_drawer("space_sim5", space_sim_params, 1);
        make_drawer("space_sim6", space_sim_params, 1);
        make_drawer("space_sim6a", space_sim_params, 1);
        make_drawer("space_sim7", space_sim_params, 1);
        make_drawer("space_sim7a", space_sim_params, 1);
        make_drawer("space_sim8", space_sim_params, 1);

        let sph_sim_params = {
            simulated: true, has_reset: true, paused: true,
        };


        make_drawer("sph_sim1", sph_sim_params);
        make_drawer("sph_sim2", sph_sim_params);
        make_drawer("sph_sim3", sph_sim_params);
        make_drawer("sph_sim5", Object.assign({ animated: true, has_draggables: true }, sph_sim_params));

        let tides_params = {
            animated: true
        };
        make_drawer("tides1", tides_params, 1, [0]);
        make_drawer("tides3", { simulated: true, has_reset: true });
        make_drawer("tides4", {}, 1, [1]);
        make_drawer("tides4a", {}, 1, [1]);
        make_drawer("tides5", tides_params, 1, [1]);
        make_drawer("tides5a", tides_params, 1, [1]);
        make_drawer("tides6", tides_params, 2, [1]);
        make_drawer("tides7", tides_params, 2, [1]);


        let tides3d_params = {
            simulated: true,
            two_axis: { vertical_limits: [-pi / 2, 0], angles: [0.0, -0.9] },
            has_draggables: true,

        };
        make_drawer("tides3d1", tides3d_params, 1);
        make_drawer("tides3d2", tides3d_params, 1);
        make_drawer("tides3d5", tides3d_params, 1);
        make_drawer("tides3d7", tides3d_params, 1);


        let m_orbit_params = {
            two_axis: { vertical_limits: [-pi / 2, 0], angles: [0.0, 0] },
            needs_eph: true,
            has_motion_blur: true,
            has_planet_scale: true,
            simulated: true,
        };

        let m_orbit_params_static = {
            two_axis: { vertical_limits: [-pi / 2, 0], angles: [0.0, 0] },
            needs_eph: true,
            has_planet_scale: true,
        }


        let m_orbit4a_params = Object.assign({}, m_orbit_params);
        m_orbit4a_params.two_axis = Object.assign({}, m_orbit_params.two_axis);
        m_orbit4a_params.two_axis.angles = [-pi / 2, -pi / 2];


        make_drawer("m_orbit1", m_orbit_params, 1, [1]);
        make_drawer("m_orbit2", Object.assign({ has_units: true }, m_orbit_params), 1, [1]);
        make_drawer("m_orbit3", Object.assign({ has_units: true, has_reset: true, reset_starts: true, }, m_orbit_params), 1, [1]);
        make_drawer("m_orbit4", m_orbit_params, 1, [1]);
        make_drawer("m_orbit4a", m_orbit4a_params, 1, [1]);
        make_drawer("m_orbit5", m_orbit_params_static, 1, [0]);
        make_drawer("m_orbit8", m_orbit_params_static, 1, [0]);
        make_drawer("m_orbit9", m_orbit_params_static, 1, [0]);


        let em_orbit_params = {
            two_axis: { vertical_limits: [-pi / 2, 0], angles: [0.0, 0] },
            needs_eph: true,
            has_planet_scale: true,
            has_motion_blur: true,
            simulated: true,
        };


        let em_orbit_params12 = Object.assign({}, em_orbit_params);
        em_orbit_params12.two_axis = { vertical_limits: [-pi / 2, 0], angles: [-pi / 2, -pi / 2] };

        make_drawer("em_orbit1", em_orbit_params, 2, [0]);
        make_drawer("em_orbit2", em_orbit_params, 2, [0]);
        make_drawer("em_orbit5", em_orbit_params, 2, [1]);
        drawers_map["em_orbit5"].drawer.set_angles(-pi / 2, -1.2);

        make_drawer("em_orbit6", em_orbit_params, 2, [1]);
        drawers_map["em_orbit6"].drawer.set_angles(-pi / 2, -1.2);

        make_drawer("em_orbit6a", em_orbit_params, 2, [1, 0]);
        make_drawer("em_orbit7", em_orbit_params, 2, [1]);
        make_drawer("em_orbit7a", em_orbit_params, 2, [1, 1]);
        make_drawer("em_orbit8", em_orbit_params, 2, [1]);
        drawers_map["em_orbit8"].drawer.set_angles(1, -0.9);

        make_drawer("em_orbit9", em_orbit_params, 2, [1]);
        make_drawer("em_orbit10", em_orbit_params, 2, [1]);
        drawers_map["em_orbit10"].drawer.set_angles(1, -0.9);

        make_drawer("em_orbit12", em_orbit_params12, 2, [1]);

        make_drawer("em_orbit20", em_orbit_params, 2, [1]);
        make_drawer("em_orbit22", em_orbit_params, 2, [1]);
        make_drawer("em_orbit25", em_orbit_params, 2, [1, 0]);
        make_drawer("em_orbit30", em_orbit_params, 2, [1]);

        make_drawer("em_orbit50", em_orbit_params, 2, [1]);

        let simple_hemi_params = {
            has_arcball: true,
        };

        make_drawer("hemi1", simple_hemi_params);
        drawers_map["hemi1"].drawer.set_rot(mat3_mul(rot_y_mat3(-0.25), mat3_mul(rot_z_mat3(-0.7), rot_x_mat3(-1.8))));

        make_drawer("hemi1a", simple_hemi_params);
        drawers_map["hemi1a"].drawer.set_rot(mat3_mul(rot_y_mat3(-0.), mat3_mul(rot_x_mat3(-1.0), rot_z_mat3(0.6))));

        make_drawer("hemi1b", simple_hemi_params);
        drawers_map["hemi1b"].drawer.set_rot(mat3_mul(rot_y_mat3(-0.25), mat3_mul(rot_z_mat3(-0.7), rot_x_mat3(-1.8))));

        make_drawer("hemi1c", simple_hemi_params);
        drawers_map["hemi1c"].drawer.set_rot(mat3_mul(rot_y_mat3(-0.0), mat3_mul(rot_x_mat3(-0.9), rot_z_mat3(0.5))));



        let rot_a = -2 * Math.PI * (0.7790572732640 + 1.00273781191135448 * (global_start_t - 2451545.0));

        let global_hemi_params = {
            two_axis: { vertical_limits: [-pi, 0], angles: [rot_a, -1.2] },
            has_draggables: true,
            has_global_location: true,
        };

        make_drawer("hemi2", global_hemi_params);
        make_drawer("hemi8", global_hemi_params);
        make_drawer("hemi10", global_hemi_params);
        make_drawer("hemi12", global_hemi_params);
        make_drawer("hemi14", global_hemi_params);
        make_drawer("hemi16", global_hemi_params);
        make_drawer("hemi20", global_hemi_params);
        make_drawer("hemi23", global_hemi_params);
        make_drawer("hemi28", global_hemi_params);
        make_drawer("hemi30", global_hemi_params).drawer.set_angles(-pi / 2, -pi / 2);
        make_drawer("hemi33", global_hemi_params).drawer.set_angles(-4.5, -pi / 2);
        make_drawer("hemi36", global_hemi_params).drawer.set_angles(-3.5, -pi / 2);;



        let sky_params = {
            two_axis: { vertical_limits: [-pi, -pi + 1.2], angles: [4, -3], drag_size_scale: 3, flip: true },
            needs_eph: true,
        };

        let unclipped_sky_params = {
            two_axis: { vertical_limits: [-pi, 0], angles: [0.0, -pi / 2], drag_size_scale: 3, flip: true },
            needs_eph: true,
            has_global_location: true,
        };

        make_drawer("sky1", Object.assign({ companion: drawers_map["hemi8"].drawer }, unclipped_sky_params), 2, [0]);

        make_drawer("sky2", Object.assign({ companion: drawers_map["hemi2"].drawer }, unclipped_sky_params), 2, [0]);
        make_drawer("sky5", sky_params);
        make_drawer("sky6", Object.assign({ companion: drawers_map["hemi1"].drawer }, sky_params));
        make_drawer("sky6a", Object.assign({ companion: drawers_map["hemi1a"].drawer }, sky_params), 1, [0]);
        make_drawer("sky6b", Object.assign({ companion: drawers_map["hemi1b"].drawer }, sky_params), 1, [0]);
        make_drawer("sky6c", Object.assign({ companion: drawers_map["hemi1c"].drawer }, unclipped_sky_params), 1, [0]);

        make_drawer("sky8", Object.assign({ companion: drawers_map["hemi10"].drawer }, unclipped_sky_params), 1, [0]);


        make_drawer("sky10", Object.assign({ companion: drawers_map["hemi12"].drawer }, unclipped_sky_params), 1, [0]);
        make_drawer("sky11", Object.assign({ companion: drawers_map["hemi14"].drawer }, unclipped_sky_params), 1, [0]);
        make_drawer("sky13", unclipped_sky_params);
        make_drawer("sky13a", unclipped_sky_params);
        make_drawer("sky14", Object.assign({ companion: drawers_map["hemi16"].drawer }, unclipped_sky_params), 1, [0]);

        make_drawer("sky20", Object.assign({ companion: drawers_map["hemi20"].drawer }, unclipped_sky_params), 2, [0]);
        make_drawer("sky23", Object.assign({ companion: drawers_map["hemi23"].drawer }, unclipped_sky_params), 2, [0]);
        let sky26 = make_drawer("sky26", unclipped_sky_params, 1, [0]);
        make_drawer("sky28", Object.assign({ companion: drawers_map["hemi28"].drawer }, unclipped_sky_params), 1, [0]);
        make_drawer("sky30", Object.assign({ companion: drawers_map["hemi30"].drawer }, unclipped_sky_params), 1, [0]);
        make_drawer("sky33", Object.assign({ companion: drawers_map["hemi33"].drawer }, unclipped_sky_params), 1, [0]);
        make_drawer("sky36", Object.assign({ companion: drawers_map["hemi36"].drawer }, unclipped_sky_params), 1, [0]);
        make_drawer("sky40", unclipped_sky_params);



        new SegmentedControl(document.getElementById("sky26_seg0"), function (x) {
            sky26.drawer.set_slider_arg(2, x);
        }, ["Northern Hemisphere", "Southern Hemisphere"]);


        // move hemis after
        eph_drawers.reverse();
        global_location_drawers.reverse();


        let grads = document.getElementsByClassName("elevation_gradient");
        for (let span of grads) {
            let str = span.innerText;
            let n = str.length;
            span.innerText = "";

            let cn = elevation_lut.length - 1;

            for (var i = 0; i < n; i++) {
                let tt = 1 + i / (n - 1) * (cn - 1);
                let i0 = floor(tt);
                let t = tt - i0;

                let i1 = min(i0 + 1, cn - 1);
                let c = vec_lerp(elevation_lut[i0], elevation_lut[i1], t);
                c = vec_scale(c, 1 / 255);
                c = vec_lerp(c, [0.5, 0.5, 0.5, 1.0], 0.1);
                let letter = document.createElement("span");
                letter.style.color = rgba_color_string(c);
                letter.innerText = str.charAt(i);
                span.appendChild(letter);
            }
        }

        if ("IntersectionObserver" in window) {

            let active_containers = [];

            window.addEventListener("scroll", (event) => {

                if (active_containers.length == 0)
                    return;

                let best_entry;
                let best_score = -1;

                if (active_containers.length > 1) {

                    for (let container of active_containers) {
                        let rect = container.getBoundingClientRect();

                        let wh = window.innerHeight || document.documentElement.clientHeight;

                        let h = rect.height;
                        let h0 = h;

                        if (rect.top < 0)
                            h += rect.top;

                        if (rect.bottom > wh)
                            h += wh - rect.bottom;

                        let score = max(0, h) / h0;

                        if (score > best_score) {
                            best_entry = container;
                            best_score = score;
                        }

                        container.drawer.set_active(false);
                    }
                } else {
                    best_entry = active_containers[0];
                }

                best_entry.drawer.set_active(true);
            });

            const observer = new IntersectionObserver(entries => {
                entries.forEach(entry => {
                    active_containers = active_containers.filter(item => item !== entry.target)
                    entry.target.drawer.set_visible(entry.isIntersecting);

                    if (entry.isIntersecting && entry.target.drawer.sph) {
                        active_containers.push(entry.target);
                    }
                });

            }, { rootMargin: "300px" })

            all_containers.forEach(container => observer.observe(container));


        } else {
            all_containers.forEach(container => container.drawer.set_visible(true));
        }

    });
})();


function switch_units() {
    metric = !metric;

    localStorage.setItem("global.metric", metric ? "true" : "false");

    if (metric)
        document.body.classList.remove("show_imperial");
    else
        document.body.classList.add("show_imperial");

    unit_drawers.forEach(drawer => drawer.request_repaint());
}


function switch_time_units() {
    short_time = !short_time;

    if (short_time)
        document.body.classList.remove("show_long_time");
    else
        document.body.classList.add("show_long_time");
}

function geolocate(drawer) {

    if (queried_lat_lon) {
        if (drawer)
            drawer.set_lat_lon(global_lat, global_lon);
        return;
    }

    const options = {
        enableHighAccuracy: false,
        timeout: 1500,
        maximumAge: Infinity,
    };

    function success(pos) {
        global_lat = pos.coords.latitude * Math.PI / 180;
        global_lon = pos.coords.longitude * Math.PI / 180;

        queried_lat_lon = true;
        document.body.classList.remove("location_querying")

        if (drawer)
            drawer.set_lat_lon(global_lat, global_lon);

        global_location_drawers.forEach(drawer => {
            drawer.request_repaint();
        });
    }

    function error(err) {
        document.body.classList.remove("location_querying")
        document.body.classList.add("location_denied");

        setTimeout(function () { document.body.classList.remove("location_denied"); }, 3000)

        console.log(err);
    }
    document.body.classList.add("location_querying")

    navigator.geolocation.getCurrentPosition(success, error, options);
}

function space_sim2_f0(e) {
    drawers_map["space_sim2"].drawer.set_draggable_pos(0, [0.72, 0.24]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(1, [0.5, 0.23]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(2, [0.26, 0.43]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(3, [0.42, 0.42]);
    drawers_map["space_sim2"].drawer.reset();

    e.preventDefault();
}

function space_sim2_f1() {
    drawers_map["space_sim2"].drawer.set_draggable_pos(0, [0.914, 0.278]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(1, [0.737, 0.257]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(2, [0.898, 0.4852]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(3, [0.801, 0.454]);
    drawers_map["space_sim2"].drawer.reset();
}
function space_sim2_f2() {
    drawers_map["space_sim2"].drawer.set_draggable_pos(0, [0.842, 0.224]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(1, [0.739, 0.265]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(2, [0.82, 0.411]);
    drawers_map["space_sim2"].drawer.set_draggable_pos(3, [0.74, 0.400]);
    drawers_map["space_sim2"].drawer.reset();

}

function space_sim5_f0() {
    drawers_map["space_sim5"].drawer.set_draggable_pos(0, [0.4, 0.15]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(1, [0.2, 0.17]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(2, [0.45, 0.3]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(3, [0.35, 0.29]);
    drawers_map["space_sim5"].drawer.reset();
    drawers_map["space_sim5"].drawer.set_paused(false, true);
}

function space_sim5_f1() {
    drawers_map["space_sim5"].drawer.set_draggable_pos(0, [0.4, 0.15]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(1, [0.2, 0.17]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(2, [0.45, 0.3]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(3, [0.35, 0.29]);
    drawers_map["space_sim5"].drawer.set_slider_arg(0, 1);
    drawers_map["space_sim5"].sliders[0].set_value(1);
}

function space_sim5_f2() {
    drawers_map["space_sim5"].drawer.set_draggable_pos(0, [0.4, 0.15]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(1, [0.2, 0.17]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(2, [0.45, 0.3]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(3, [0.35, 0.29]);
    drawers_map["space_sim5"].drawer.set_slider_arg(0, 0);
    drawers_map["space_sim5"].sliders[0].set_value(0);
}

function space_sim5_f3() {
    drawers_map["space_sim5"].drawer.set_draggable_pos(0, [0.4, 0.15]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(1, [0.2, 0.17]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(2, [0.45, 0.3]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(3, [0.35, 0.29]);
    drawers_map["space_sim5"].drawer.set_slider_arg(0, 0.5);
    drawers_map["space_sim5"].sliders[0].set_value(0.5);
}

function space_sim5_f4() {
    let d = Math.random() * 0.9 + 0.05;
    drawers_map["space_sim5"].drawer.set_draggable_pos(0, [0.4, 0.15]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(1, [0.2, 0.17]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(2, [0.45, 0.3]);
    drawers_map["space_sim5"].drawer.set_draggable_pos(3, [0.35, 0.29]);
    drawers_map["space_sim5"].drawer.set_slider_arg(0, d);
    drawers_map["space_sim5"].sliders[0].set_value(d);
}

function space_sim6_f0() {
    drawers_map["space_sim6"].drawer.set_slider_arg(0, 0.75);
    drawers_map["space_sim6"].sliders[0].set_value(0.75);
}

function space_sim6a_f0() {
    drawers_map["space_sim6a"].drawer.set_slider_arg(0, 0.75);
    drawers_map["space_sim6a"].sliders[0].set_value(0.75);
    drawers_map["space_sim6a"].drawer.set_paused(false, true);
}

function space_sim7_f0() {
    drawers_map["space_sim7"].drawer.set_draggable_pos(0, [0.4, 0.1]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(1, [0.21, 0.1]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(2, [0.45, 0.4]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(3, [0.35, 0.37]);
    drawers_map["space_sim7"].drawer.reset();
}

function space_sim7_f1() {
    drawers_map["space_sim7"].drawer.set_draggable_pos(0, [0.4, 0.15]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(1, [0.2, 0.17]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(2, [0.45, 0.3]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(3, [0.35, 0.29]);
    drawers_map["space_sim7"].drawer.reset();

}

function space_sim7_f2() {
    drawers_map["space_sim7"].drawer.set_draggable_pos(0, [0.44, 0.13]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(1, [0.19, 0.13]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(2, [0.44, 0.3]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(3, [0.35, 0.3]);
    drawers_map["space_sim7"].drawer.reset();

}

function space_sim7_f3() {
    drawers_map["space_sim7"].drawer.set_draggable_pos(0, [0.417, 0.092]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(1, [0.319, 0.07]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(2, [0.339, 0.362]);
    drawers_map["space_sim7"].drawer.set_draggable_pos(3, [0.287, 0.402]);
    drawers_map["space_sim7"].drawer.reset();

}

function space_sim7_f4() {
    drawers_map["space_sim7"].drawer.set_slider_arg(0, 0);
    drawers_map["space_sim7"].sliders[0].set_value(0);
}

function space_sim7_f5() {
    drawers_map["space_sim7"].drawer.set_slider_arg(0, 1);
    drawers_map["space_sim7"].sliders[0].set_value(1);
}

function ellipse2_f0() {
    drawers_map["ellipse2"].drawer.set_slider_arg(0, 1);
    drawers_map["ellipse2"].sliders[0].set_value(1);
}

function ellipse2_f1() {
    drawers_map["ellipse2"].drawer.set_slider_arg(0, 0.25);
    drawers_map["ellipse2"].sliders[0].set_value(0.25);
}

function angular_momentum_f0() {
    drawers_map["angular_momentum"].drawer.set_slider_arg(0, 0.1);
    drawers_map["angular_momentum"].sliders[0].set_value(0.1);
}

function angular_momentum_f1() {
    drawers_map["angular_momentum"].drawer.set_slider_arg(0, 0.9);
    drawers_map["angular_momentum"].sliders[0].set_value(0.9);
}

function earth_scale_f0() {
    drawers_map["earth_scale"].drawer.set_slider_arg(0, 1);
    drawers_map["earth_scale"].sliders[0].set_value(1);
}


function m_orbit3_f0() {
    drawers_map["m_orbit3"].drawer.set_angles(undefined, 0);
}


function m_orbit4_f0() {
    drawers_map["m_orbit4"].drawer.set_angles(undefined, -Math.PI / 2);
}

function m_orbit4_f1() {
    drawers_map["m_orbit4"].drawer.set_angles(undefined, 0);
}

function m_orbit9_f0() {
    drawers_map["m_orbit9"].drawer.set_angles(undefined, 0);
}

function m_orbit9_f1() {
    drawers_map["m_orbit9"].drawer.set_angles(undefined, -Math.PI / 2);
}

function sky10_f0() {
    drawers_map["sky10"].drawer.set_lat_lon(0, undefined);
}

function sky10_f1() {
    drawers_map["sky10"].drawer.set_lat_lon(Math.PI / 2, undefined);
}

function sky10_f2() {
    drawers_map["sky10"].drawer.set_lat_lon(-Math.PI / 2, undefined);
}

function sky11_f0() {
    drawers_map["sky11"].drawer.set_lat_lon(Math.PI / 2, undefined);
}

function sky30_f0() {

    drawers_map["sky30"].drawer.set_lat_lon(32.4748888 * Math.PI / 180, -96.2764444 * Math.PI / 180);
    drawers_map["sky30"].drawer.set_slider_arg(0, 0.4);
    drawers_map["sky30"].sliders[0].set_value(0.4);
}



function sky33_f0() {
    drawers_map["sky33"].drawer.set_lat_lon(35.0844 * Math.PI / 180, -106.6504 * Math.PI / 180);
    drawers_map["sky33"].drawer.set_slider_arg(0, 0.468);
    drawers_map["sky33"].sliders[0].set_value(0.468);
}


function em_orbit2_f0() {
    drawers_map["em_orbit2"].drawer.set_angles(undefined, 0);
    drawers_map["em_orbit2"].drawer.set_slider_arg(0, 0);
    drawers_map["em_orbit2"].sliders[0].set_value(0);
}

function em_orbit2_f1() {
    drawers_map["em_orbit2"].drawer.set_angles(undefined, -Math.PI / 2);
}

function em_orbit2_f2() {
    drawers_map["em_orbit2"].drawer.set_angles(undefined, -Math.PI / 2);
    drawers_map["em_orbit2"].drawer.set_slider_arg(0, 1);
    drawers_map["em_orbit2"].sliders[0].set_value(1);
}


function em_orbit7_f0() {
    drawers_map["em_orbit7"].drawer.set_slider_arg(1, 1);
    drawers_map["em_orbit7"].sliders[1].set_value(1);
}


function em_orbit7a_f0() {
    drawers_map["em_orbit7a"].drawer.set_angles(undefined, 0);
}

function shadow_f0() {
    drawers_map["shadow"].drawer.set_draggable_pos(0, [0.42, 0.15]);
}

function shadow_f1() {
    drawers_map["shadow"].drawer.set_draggable_pos(0, [0.42, 0.17]);
}

function shadow_f2() {
    drawers_map["shadow"].drawer.set_draggable_pos(0, [0.42, 0.2]);
}


function brdf1_f0() {

    let a = (drawers_map["brdf1"].drawer.slider_args[0] - 0.5) * 3.5;
    let mat = rot_y_mat3(-a - Math.PI / 2);
    drawers_map["brdf1"].drawer.set_rot(mat);
}

function brdf2_f0() {

    let a = (drawers_map["brdf2"].drawer.slider_args[0] - 0.5) * 3.5;
    let mat = rot_y_mat3(-a - Math.PI / 2 - 0.5);
    drawers_map["brdf2"].drawer.set_rot(mat);
}

function brdf2_f1() {

    let a = (drawers_map["brdf2"].drawer.slider_args[0] - 0.5) * 3.5;
    let mat = rot_y_mat3(-a - Math.PI / 2 - 0.25);
    drawers_map["brdf2"].drawer.set_rot(mat);
}

function brdf2_f2() {

    let a = (drawers_map["brdf2"].drawer.slider_args[0] - 0.5) * 3.5;
    let mat = rot_y_mat3(-a - Math.PI / 2);
    drawers_map["brdf2"].drawer.set_rot(mat);
}


function brdf3_f0() {

    let a = (drawers_map["brdf3"].drawer.slider_args[0] - 0.5) * 3.5;
    let mat = rot_y_mat3(-a + Math.PI / 2);
    drawers_map["brdf3"].drawer.set_rot(mat);
}

function brdf3_f1() {

    let a = (drawers_map["brdf3"].drawer.slider_args[0] - 0.5) * 3.5;
    let mat = rot_y_mat3(-a - Math.PI / 2 - 0.02);
    drawers_map["brdf3"].drawer.set_rot(mat);
}


function shadow_hiding_f0() {

    let a = (drawers_map["shadow_hiding"].drawer.slider_args[0] - 0.5) * Math.PI * 0.84;
    drawers_map["shadow_hiding"].drawer.set_angles(a < 0 ? Math.PI / 2 : -Math.PI / 2, -Math.abs(a));
}

function shadow_hiding2_f0() {

    drawers_map["shadow_hiding2"].drawer.set_angles(0, -1.2);
}

function shadow_hiding2_f1() {

    let a = (drawers_map["shadow_hiding2"].drawer.slider_args[0] - 0.5) * Math.PI * 0.84;
    drawers_map["shadow_hiding2"].drawer.set_angles(a < 0 ? Math.PI / 2 : -Math.PI / 2, -Math.abs(a));
}

function shadow_hiding2_f2() {
    drawers_map["shadow_hiding2"].drawer.set_slider_arg(0, 0);
    drawers_map["shadow_hiding2"].sliders[0].set_value(0);
    let a = (-0.5) * Math.PI * 0.84;
    drawers_map["shadow_hiding2"].drawer.set_angles(a < 0 ? Math.PI / 2 : -Math.PI / 2, -Math.abs(a));
}

function tides3d5_f0() {
    drawers_map["tides3d5"].drawer.set_lat_lon(0, undefined);
}


function tides3d5_f1() {
    drawers_map["tides3d5"].drawer.set_lat_lon(1.3, undefined);
}

function tides3d5_f2() {
    drawers_map["tides3d5"].drawer.set_lat_lon(0, undefined);
    drawers_map["tides3d5"].drawer.set_angles(0, 0);
}



function em4a_f0() {
    drawers_map["em4a"].drawer.set_slider_arg(2, 1);
    em4a_seg.set_selection(1);
}

function em4a_f1() {
    drawers_map["em4a"].drawer.set_slider_arg(2, 2);
    em4a_seg.set_selection(2);
}

function em4a_f2() {
    drawers_map["em4a"].drawer.set_slider_arg(2, 2);
    drawers_map["em4a"].drawer.set_slider_arg(1, 0.5);
    drawers_map["em4a"].sliders[1].set_value(0.5);
    em4a_seg.set_selection(2);
}

function em5_f0() {
    drawers_map["em5"].drawer.set_slider_arg(0, 0.5);
    drawers_map["em5"].sliders[0].set_value(0.5);
}

function em5_f1() {
    let d = Math.random();
    drawers_map["em5"].drawer.set_slider_arg(0, d);
    drawers_map["em5"].sliders[0].set_value(d);
}