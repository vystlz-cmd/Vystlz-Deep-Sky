"""
VYSTLZ DEEP SKY  --  v3.0
=========================
A free-roam sky-survey / anomaly-scanning sandbox. You operate a ground
receiver array: pan the sky, tune the redshift band, pick a sensor mode,
pick a tool, and scan whatever the array can lock onto.

Everything is drawn procedurally with pygame primitives and every sound is
synthesized at runtime with numpy. No external assets, no internet, one file.

There are no fail states. Nothing chases you. Nothing kills you.

CONTROLS
--------
  WASD / arrows     pan the sky (hold SHIFT to move fast)
  Mouse             aim the reticle
  LMB (hold)        scan whatever is under the reticle
  Mouse wheel       zoom          |  MMB drag: pan
  Q / E             turn the Z dial (SHIFT = coarse, or drag / scroll the dial)
  Z                 snap the dial back to z = 0 (local sky)
  1 / 2 / 3         sensor mode: VISUAL / THERMAL / RADIO
  4 / 5 / 6 / 7     tools: SPECTRO / POLARI / INTERF / RANGE
  8 / 9             tools: PHOTO / CMB
  0                 FINDER CHART (full-sky map)
  X (hold)          radial tool menu -- flick to pick, release to confirm
  R                 toggle MONITOR-scan crosshair (hold LMB to link a live graph)
  TAB               cycle the side panel tabs (LOG / DATA / CALIB / HELP)
  LEFT/RIGHT in HELP  cycle help sub-pages (CONTROLS / TOOLS / SCIENCE / ANOM.)
  F                 cycle the log filter (ALL / STARS / ANOMALIES / SYSTEM)
  F5 / F9           quick save / quick load
  K                 open CODEX (field guide)
  M or ESC          pause menu (save, load, settings, quit)

SCANNING
--------
Objects answer on different bands and to different tools. A red giant is
loudest on THERMAL, a quasar on RADIO, most stars on VISUAL. Wrong band,
slow scan. Wrong tool, missing detail.

Anomalies take two passes: the first CLASSIFIES the contact, and after a few
in-game hours the array can RESOLVE it for the real log entry. Revisit them.

CHAINS
------
Some anomalies belong to a chain. Resolving one link reveals a bearing, not
a map pin -- a directional chevron on the edge of the sky view shows you
which way to pan, and a bearing readout tells you the angle. Follow them.

REDSHIFT
--------
The dial tunes the receiver to a redshift band. Local stars sit at z = 0.
Everything further out is riding the expansion of space: its light is
stretched by (1+z), so it only answers when the dial is near its band.
Turn the dial up and the local sky fades out and the deep universe fades in,
all the way to z = 1089 -- the cosmic microwave background, the wall at the
edge of everything observable.
"""

import os
import sys
import json
import math
import time
import random
import hashlib
import socket
import subprocess
import datetime

import pygame

try:
    import numpy as np
    HAVE_NUMPY = True
except Exception:
    HAVE_NUMPY = False


# ==========================================================================
# CONFIG
# ==========================================================================

VERSION = "3.0"
TITLE = "VYSTLZ DEEP SKY"

FPS = 60
REAL_SECONDS_PER_GAME_HOUR = 14.0

MONITOR_SLOTS = 3
MONITOR_HIST_LEN = 64
MONITOR_SAMPLE_DT = 0.15
DIAL_SWEEP_DEG = 132.0

SAVE_DIR = os.path.join(os.path.expanduser("~"), ".vystlz_deep_sky")
SAVE_SLOTS = 4

HORROR_DURATION = 9.0
NOTICE_REVEAL_DURATION = 5.0   # how long the player gets to read/hear the
                                # noticer before the static takeover begins
NOTICE_APPROACH_DURATION = 3.4  # the drag-in: camera and cursor are hauled
                                 # toward the physical contact before it
                                 # writes anything to the log
NOTICE_APPROACH_ZOOM = 24.0     # how tight the array locks in during the drag
NOTICE_MSG = "WE CAST THIS MESSAGE INTO THE COSMOS. HELLO, {host}."

# palette -- phosphor CRT
BG          = (3, 7, 6)
BG_PANEL    = (4, 13, 10)
PHOS        = (120, 255, 186)
PHOS_DIM    = (52, 128, 100)
PHOS_FAINT  = (24, 62, 50)
AMBER       = (255, 178, 64)
AMBER_DIM   = (138, 96, 36)
RED_WARN    = (255, 78, 72)
VIOLET      = (186, 148, 255)
VIOLET_DIM  = (96, 76, 150)
CYAN        = (120, 220, 255)
WHITE_STAR  = (236, 245, 255)

MODE_COLORS = {"VISUAL": PHOS, "THERMAL": AMBER, "RADIO": VIOLET}
MODES = ["VISUAL", "THERMAL", "RADIO"]

# tools keyed 4-9; 0 opens the finder chart (not a persistent tool)
TOOLS = ["SPECTRO", "POLARI", "INTERF", "RANGE", "PHOTO", "CMB"]
TOOL_COLORS = {"SPECTRO": CYAN, "POLARI": VIOLET, "INTERF": PHOS,
               "RANGE": AMBER, "PHOTO": WHITE_STAR, "CMB": RED_WARN}
TOOL_KEYS = {pygame.K_4: "SPECTRO", pygame.K_5: "POLARI",
             pygame.K_6: "INTERF", pygame.K_7: "RANGE",
             pygame.K_8: "PHOTO", pygame.K_9: "CMB"}

FONT_CANDIDATES = "Consolas,Cascadia Mono,Courier New,DejaVu Sans Mono,Liberation Mono,monospace"

SW, SH = 1280, 760


# ==========================================================================
# COSMOLOGY  (flat LCDM, Planck-ish parameters)
# ==========================================================================

H0 = 67.7
OMEGA_M = 0.310
OMEGA_L = 0.690
C_KMS = 299792.458
HUBBLE_TIME_GYR = 977.79 / H0
HUBBLE_DIST_MPC = C_KMS / H0
MPC_TO_MLY = 3.26156

_COS_Z = []
_COS_DC = []
_COS_TL = []


def _E(z):
    return math.sqrt(OMEGA_M * (1.0 + z) ** 3 + OMEGA_L)


def _build_cosmology_tables():
    global _COS_Z, _COS_DC, _COS_TL
    zmax, steps = 1200.0, 6000
    zs = [0.0]
    for i in range(1, steps + 1):
        zs.append(math.exp(math.log(1e-4) + (math.log(zmax) - math.log(1e-4)) * i / steps))
    dc, tl = 0.0, 0.0
    _COS_Z, _COS_DC, _COS_TL = [0.0], [0.0], [0.0]
    for i in range(1, len(zs)):
        z0, z1 = zs[i - 1], zs[i]
        dz = z1 - z0
        zm = 0.5 * (z0 + z1)
        dc += HUBBLE_DIST_MPC * dz / _E(zm)
        tl += HUBBLE_TIME_GYR * dz / ((1.0 + zm) * _E(zm))
        _COS_Z.append(z1)
        _COS_DC.append(dc)
        _COS_TL.append(tl)


def _interp(z, table):
    if z <= 0:
        return 0.0
    lo, hi = 0, len(_COS_Z) - 1
    if z >= _COS_Z[hi]:
        return table[hi]
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if _COS_Z[mid] < z:
            lo = mid
        else:
            hi = mid
    span = _COS_Z[hi] - _COS_Z[lo]
    t = 0.0 if span <= 0 else (z - _COS_Z[lo]) / span
    return table[lo] + (table[hi] - table[lo]) * t


def comoving_mpc(z):
    return _interp(z, _COS_DC)


def lookback_gyr(z):
    return _interp(z, _COS_TL)


def light_travel_mly(z):
    return lookback_gyr(z) * 1000.0


def recession_kms(z):
    a = (1.0 + z) ** 2
    return C_KMS * (a - 1.0) / (a + 1.0)


def scale_factor(z):
    return 1.0 / (1.0 + z)


def z_from_distance_mly(d_mly):
    target = d_mly / MPC_TO_MLY
    lo, hi = 0.0, 1200.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if comoving_mpc(mid) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def wavelength_shift(rest_nm, z):
    return rest_nm * (1.0 + z)


SPECTRAL_LINES = [
    ("Ly-alpha", 121.567, VIOLET),
    ("Ca II K", 393.37, CYAN),
    ("H-delta", 410.17, CYAN),
    ("H-gamma", 434.05, CYAN),
    ("H-beta", 486.13, PHOS),
    ("O III", 500.70, PHOS),
    ("Na I D", 589.29, AMBER),
    ("H-alpha", 656.28, RED_WARN),
    ("S II", 671.60, RED_WARN),
]


def band_label(nm):
    if nm < 10:
        return "X-RAY"
    if nm < 380:
        return "UV"
    if nm < 750:
        return "OPTICAL"
    if nm < 1e6:
        return "INFRARED"
    return "MICROWAVE"


# ==========================================================================
# CATALOGS
# ==========================================================================

def spectral_color(sp):
    table = {
        "O": (155, 176, 255), "B": (185, 205, 255), "A": (220, 230, 255),
        "F": (250, 248, 240), "G": (255, 238, 195), "K": (255, 200, 145),
        "M": (255, 150, 110), "C": (255, 130, 95),
    }
    return table.get(sp[:1].upper(), (230, 236, 255))


STARS_RAW = [
    ("Sol", 0.0, 0.0, 0.0000158, -26.7, "G"),
    ("Proxima Centauri", 14.4959, -62.6795, 4.25, 11.13, "M"),
    ("Alpha Centauri A", 14.6600, -60.8354, 4.37, -0.01, "G"),
    ("Barnard's Star", 17.9636, 4.6933, 5.96, 9.51, "M"),
    ("Wolf 359", 10.7434, 7.0145, 7.86, 13.54, "M"),
    ("Lalande 21185", 11.0531, 35.9698, 8.31, 7.52, "M"),
    ("Sirius", 6.7525, -16.7161, 8.60, -1.46, "A"),
    ("Luyten 726-8", 1.6390, -17.9570, 8.73, 12.99, "M"),
    ("Ross 154", 18.8299, -23.8362, 9.70, 10.44, "M"),
    ("Ross 248", 23.6958, 44.1770, 10.30, 12.29, "M"),
    ("Epsilon Eridani", 3.5486, -9.4583, 10.48, 3.73, "K"),
    ("Lacaille 9352", 23.0929, -35.8531, 10.72, 7.34, "M"),
    ("Ross 128", 11.7979, 0.8047, 11.01, 11.13, "M"),
    ("61 Cygni A", 21.0669, 38.7497, 11.40, 5.21, "K"),
    ("Procyon", 7.6550, 5.2250, 11.46, 0.34, "F"),
    ("Struve 2398", 18.7098, 59.6317, 11.49, 8.90, "M"),
    ("Groombridge 34", 0.3038, 44.0231, 11.62, 8.08, "M"),
    ("Epsilon Indi", 22.0532, -56.7850, 11.87, 4.69, "K"),
    ("Tau Ceti", 1.7344, -15.9375, 11.91, 3.50, "G"),
    ("YZ Ceti", 1.2199, -16.9986, 12.13, 12.02, "M"),
    ("Luyten's Star", 7.4569, 5.2256, 12.36, 9.87, "M"),
    ("Kapteyn's Star", 5.1959, -44.9990, 12.83, 8.85, "M"),
    ("Lacaille 8760", 21.1743, -38.8719, 12.95, 6.67, "M"),
    ("Kruger 60", 22.4796, 57.6969, 13.08, 9.79, "M"),
    ("Ross 614", 6.4977, -2.8135, 13.35, 11.15, "M"),
    ("Wolf 1061", 16.5052, -12.6620, 13.82, 10.10, "M"),
    ("Van Maanen's Star", 0.8199, 5.3906, 14.07, 12.38, "F"),
    ("Gliese 1", 0.0899, -37.3572, 14.22, 8.55, "M"),
    ("Gliese 581", 15.3253, -7.7128, 20.42, 10.57, "M"),
    ("Gliese 876", 22.9532, -14.2625, 15.24, 10.17, "M"),
    ("TRAPPIST-1", 23.1083, -5.0414, 40.70, 18.80, "M"),
    ("40 Eridani", 4.2555, -7.6528, 16.26, 4.43, "K"),
    ("70 Ophiuchi", 18.0956, 2.5000, 16.59, 4.03, "K"),
    ("Altair", 19.8464, 8.8683, 16.73, 0.76, "A"),
    ("Sigma Draconis", 19.5822, 69.6611, 18.80, 4.68, "K"),
    ("Eta Cassiopeiae", 0.8188, 57.8156, 19.32, 3.44, "G"),
    ("82 Eridani", 3.3320, -43.0699, 19.71, 4.26, "G"),
    ("Delta Pavonis", 20.1451, -66.1820, 19.92, 3.56, "G"),
    ("Xi Bootis", 14.8613, 19.1005, 21.90, 4.55, "G"),
    ("51 Pegasi", 22.9602, 20.7686, 50.45, 5.49, "G"),
    ("HD 209458", 22.0521, 18.8842, 159.0, 7.65, "G"),
    ("Kepler-186", 19.9169, 43.9553, 579.0, 14.62, "M"),
    ("Kepler-452", 19.7726, 44.2778, 1800.0, 13.43, "G"),
    ("Fomalhaut", 22.9608, -29.6222, 25.13, 1.16, "A"),
    ("Vega", 18.6156, 38.7837, 25.04, 0.03, "A"),
    ("Pollux", 7.7553, 28.0262, 33.78, 1.14, "K"),
    ("Arcturus", 14.2610, 19.1824, 36.71, -0.05, "K"),
    ("Chara", 12.5622, 41.3576, 27.53, 4.26, "G"),
    ("Muphrid", 13.9114, 18.3979, 37.00, 2.68, "G"),
    ("Denebola", 11.8177, 14.5720, 35.90, 2.11, "A"),
    ("Capella", 5.2782, 45.9980, 42.92, 0.08, "G"),
    ("Castor", 7.5766, 31.8883, 51.00, 1.58, "A"),
    ("Caph", 0.1529, 59.1498, 54.70, 2.27, "F"),
    ("Alpha Cephei", 21.3097, 62.5856, 49.00, 2.46, "A"),
    ("Menkent", 14.1114, -36.3700, 61.00, 2.06, "K"),
    ("Regulus", 10.1395, 11.9672, 79.30, 1.40, "B"),
    ("Algieba", 10.3328, 19.8415, 130.0, 2.08, "K"),
    ("Zosma", 11.2351, 20.5237, 58.40, 2.56, "A"),
    ("Chort", 11.2373, 15.4297, 165.0, 3.32, "A"),
    ("Epsilon Leonis", 9.7640, 23.7742, 247.0, 2.98, "G"),
    ("Eta Leonis", 10.1224, 16.7627, 1270.0, 3.48, "A"),
    ("Aldebaran", 4.5987, 16.5093, 65.30, 0.85, "K"),
    ("Alcyone", 3.7914, 24.1052, 440.0, 2.87, "B"),
    ("Elnath", 5.4381, 28.6075, 134.0, 1.65, "B"),
    ("Zeta Tauri", 5.6273, 21.1426, 440.0, 3.00, "B"),
    ("Alphecca", 15.5781, 26.7147, 75.00, 2.22, "A"),
    ("Izar", 14.7497, 27.0742, 203.0, 2.37, "K"),
    ("Seginus", 14.5346, 38.3082, 86.80, 3.03, "A"),
    ("Nekkar", 15.0322, 40.3906, 225.0, 3.49, "G"),
    ("Mizar", 13.3988, 54.9254, 82.90, 2.23, "A"),
    ("Alkaid", 13.7923, 49.3133, 103.9, 1.85, "B"),
    ("Alioth", 12.9005, 55.9598, 82.60, 1.77, "A"),
    ("Megrez", 12.2571, 57.0326, 80.50, 3.31, "A"),
    ("Phecda", 11.8972, 53.6948, 83.20, 2.41, "A"),
    ("Merak", 11.0307, 56.3824, 79.70, 2.37, "A"),
    ("Dubhe", 11.0621, 61.7510, 123.0, 1.79, "K"),
    ("Polaris", 2.5303, 89.2641, 447.0, 1.98, "F"),
    ("Schedar", 0.6751, 56.5373, 228.0, 2.24, "K"),
    ("Gamma Cassiopeiae", 0.9451, 60.7167, 550.0, 2.47, "B"),
    ("Ruchbah", 1.4303, 60.2353, 99.40, 2.68, "A"),
    ("Segin", 1.9065, 63.6701, 410.0, 3.35, "B"),
    ("Mirfak", 3.4054, 49.8612, 510.0, 1.79, "F"),
    ("Algol", 3.1362, 40.9556, 92.80, 2.12, "B"),
    ("Zeta Persei", 3.9022, 31.8836, 750.0, 2.85, "B"),
    ("Almach", 2.0650, 42.3297, 350.0, 2.10, "K"),
    ("Mirach", 1.1622, 35.6206, 197.0, 2.05, "M"),
    ("Alpheratz", 0.1398, 29.0904, 97.00, 2.06, "B"),
    ("Algenib", 0.2206, 15.1836, 470.0, 2.83, "B"),
    ("Markab", 23.0793, 15.2053, 133.0, 2.48, "B"),
    ("Scheat", 23.0629, 28.0828, 196.0, 2.42, "M"),
    ("Enif", 21.7364, 9.8750, 690.0, 2.38, "K"),
    ("Diphda", 0.7264, -17.9866, 96.00, 2.01, "K"),
    ("Menkar", 3.0380, 4.0897, 250.0, 2.53, "M"),
    ("Mira", 2.3224, -2.9776, 300.0, 3.04, "M"),
    ("Hamal", 2.1195, 23.4624, 65.80, 2.00, "K"),
    ("Achernar", 1.6286, -57.2368, 139.0, 0.46, "B"),
    ("Acamar", 2.9710, -40.3047, 161.0, 3.20, "A"),
    ("Rigel", 5.2423, -8.2016, 863.0, 0.13, "B"),
    ("Betelgeuse", 5.9195, 7.4071, 548.0, 0.50, "M"),
    ("Bellatrix", 5.4188, 6.3497, 250.0, 1.64, "B"),
    ("Saiph", 5.7959, -9.6696, 650.0, 2.09, "B"),
    ("Meissa", 5.5855, 9.9342, 1100.0, 3.39, "O"),
    ("Alnitak", 5.6793, -1.9426, 1260.0, 1.77, "O"),
    ("Alnilam", 5.6036, -1.2019, 1340.0, 1.69, "B"),
    ("Mintaka", 5.5334, -0.2991, 1200.0, 2.23, "O"),
    ("Mirzam", 6.3783, -17.9559, 500.0, 1.98, "B"),
    ("Wezen", 7.1399, -26.3932, 1600.0, 1.83, "F"),
    ("Adhara", 6.9771, -28.9721, 430.0, 1.50, "B"),
    ("Aludra", 7.4015, -29.3031, 2000.0, 2.45, "B"),
    ("Alhena", 6.6285, 16.3993, 109.0, 1.93, "A"),
    ("Mebsuta", 6.7324, 25.1311, 840.0, 2.98, "G"),
    ("Tejat", 6.3828, 22.5137, 230.0, 2.87, "M"),
    ("Canopus", 6.3992, -52.6957, 310.0, -0.74, "F"),
    ("Miaplacidus", 9.2200, -69.7172, 113.0, 1.67, "A"),
    ("Avior", 8.3752, -59.5096, 630.0, 1.86, "K"),
    ("Aspidiske", 9.2850, -59.2753, 690.0, 2.21, "A"),
    ("Eta Carinae", 10.7515, -59.6845, 7500.0, 4.30, "O"),
    ("Acrux", 12.4433, -63.0991, 320.0, 0.76, "B"),
    ("Mimosa", 12.7953, -59.6888, 280.0, 1.25, "B"),
    ("Gacrux", 12.5194, -57.1133, 88.60, 1.63, "M"),
    ("Delta Crucis", 12.2525, -58.7489, 345.0, 2.75, "B"),
    ("Hadar", 14.0637, -60.3730, 390.0, 0.61, "B"),
    ("Spica", 13.4199, -11.1613, 250.0, 0.97, "B"),
    ("Vindemiatrix", 13.0362, 10.9591, 109.0, 2.83, "G"),
    ("Antares", 16.4901, -26.4320, 550.0, 0.96, "M"),
    ("Shaula", 17.5601, -37.1038, 570.0, 1.62, "B"),
    ("Lesath", 17.5122, -37.2958, 580.0, 2.70, "B"),
    ("Sargas", 17.6220, -42.9978, 270.0, 1.86, "F"),
    ("Dschubba", 16.0056, -22.6217, 400.0, 2.29, "B"),
    ("Graffias", 16.0906, -19.8054, 400.0, 2.62, "B"),
    ("Pi Scorpii", 15.9810, -26.1140, 590.0, 2.89, "B"),
    ("Rasalhague", 17.5822, 12.5600, 48.60, 2.08, "A"),
    ("Rasalgethi", 17.2443, 14.3903, 360.0, 3.35, "M"),
    ("Unukalhai", 15.7378, 6.4256, 74.00, 2.63, "K"),
    ("Kaus Australis", 18.4029, -34.3846, 143.0, 1.85, "B"),
    ("Kaus Media", 18.3499, -29.8281, 306.0, 2.70, "K"),
    ("Kaus Borealis", 18.4661, -25.4217, 78.00, 2.82, "K"),
    ("Nunki", 18.9211, -26.2967, 228.0, 2.05, "B"),
    ("Ascella", 19.0436, -29.8803, 88.00, 2.60, "A"),
    ("Phi Sagittarii", 18.7630, -26.9907, 231.0, 3.17, "B"),
    ("Deneb", 20.6905, 45.2803, 2615.0, 1.25, "A"),
    ("Sadr", 20.3705, 40.2567, 1800.0, 2.23, "F"),
    ("Gienah Cygni", 20.7702, 33.9703, 72.70, 2.48, "K"),
    ("Delta Cygni", 19.7495, 45.1308, 165.0, 2.87, "B"),
    ("Albireo", 19.5121, 27.9597, 430.0, 3.18, "K"),
    ("Sheliak", 18.8346, 33.3627, 960.0, 3.52, "B"),
    ("Sulafat", 18.9823, 32.6896, 620.0, 3.25, "B"),
    ("Tarazed", 19.7709, 10.6133, 395.0, 2.72, "K"),
    ("Alshain", 19.9219, 6.4068, 44.70, 3.71, "G"),
    ("Eltanin", 17.9434, 51.4889, 154.0, 2.23, "K"),
    ("Thuban", 14.0731, 64.3758, 303.0, 3.65, "A"),
    ("Alnair", 22.1372, -46.9610, 101.0, 1.74, "B"),
    ("Peacock", 20.4275, -56.7351, 179.0, 1.94, "B"),
    ("Atria", 16.8111, -69.0277, 391.0, 1.91, "K"),
    ("Delta Cephei", 22.4907, 58.4152, 887.0, 3.95, "F"),
    ("Mu Cephei", 21.7247, 58.7800, 2840.0, 4.08, "M"),
    ("Alphard", 9.4597, -8.6586, 177.0, 1.98, "K"),
    ("Sadalsuud", 21.5250, -5.5712, 540.0, 2.90, "G"),
    ("Sadalmelik", 22.0964, -0.3200, 520.0, 2.94, "G"),
    ("Gomeisa", 7.4527, 8.2893, 160.0, 2.89, "B"),
    ("Zubenelgenubi", 14.8479, -16.0418, 77.00, 2.75, "A"),
    ("Zubeneschamali", 15.2830, -9.3829, 185.0, 2.61, "B"),
    ("Cor Caroli", 12.9338, 38.3186, 115.0, 2.90, "A"),
]

DEEP_SKY_RAW = [
    ("Large Magellanic Cloud", 5.3933, -69.7561, 0.00093, "galaxy", "VISUAL",
     "Satellite galaxy, 163,000 ly. Close enough that its individual stars resolve."),
    ("Small Magellanic Cloud", 0.8771, -72.8286, 0.00053, "galaxy", "VISUAL",
     "Second satellite, 200,000 ly, visibly being pulled apart by the Milky Way."),
    ("M31 Andromeda", 0.7123, 41.2687, -0.00100, "galaxy", "VISUAL",
     "2.5 Mly. Blueshifted: it is falling toward us at 300 km/s and will arrive in 4 Gyr."),
    ("M33 Triangulum", 1.5641, 30.6602, -0.00060, "galaxy", "VISUAL",
     "2.7 Mly. Third-largest member of the Local Group, also approaching."),
    ("NGC 253 Sculptor", 0.7925, -25.2883, 0.00081, "galaxy", "THERMAL",
     "11.4 Mly. A starburst galaxy: enormous dust lanes glowing in infrared."),
    ("M81 Bode's Galaxy", 9.9258, 69.0653, -0.00011, "galaxy", "VISUAL",
     "11.8 Mly. Grand-design spiral, gravitationally locked with M82."),
    ("M82 Cigar Galaxy", 9.9310, 69.6806, 0.00068, "galaxy", "THERMAL",
     "12 Mly. Venting superheated gas out of both poles at 1000 km/s."),
    ("Centaurus A", 13.4243, -43.0191, 0.00183, "galaxy", "RADIO",
     "13 Mly. Radio lobes a million light years across, fed by a central black hole."),
    ("M51 Whirlpool", 13.4979, 47.1952, 0.00154, "galaxy", "VISUAL",
     "23 Mly. Spiral arms sharpened by a small companion galaxy passing through."),
    ("M101 Pinwheel", 14.0535, 54.3488, 0.00080, "galaxy", "VISUAL",
     "21 Mly. Face-on spiral, unusually large and unusually lopsided."),
    ("M104 Sombrero", 12.6665, -11.6231, 0.00342, "galaxy", "VISUAL",
     "29 Mly. Dust lane seen edge-on, ringing a huge bulge of old stars."),
    ("M87 Virgo A", 12.5137, 12.3911, 0.00428, "galaxy", "RADIO",
     "53 Mly. Its central black hole was the first ever imaged directly."),
    ("M77 Cetus A", 2.7114, -0.0133, 0.00379, "galaxy", "RADIO",
     "47 Mly. Seyfert nucleus: a bright, actively feeding core in an ordinary spiral."),
    ("Virgo Cluster", 12.4500, 12.7200, 0.00380, "cluster", "VISUAL",
     "1300+ galaxies at 54 Mly. The nearest thing to us that deserves the word cluster."),
    ("Fornax Cluster", 3.6400, -35.4500, 0.00475, "cluster", "VISUAL",
     "Compact southern cluster, 62 Mly, dominated by smooth elliptical galaxies."),
    ("Perseus Cluster", 3.3300, 41.5117, 0.01756, "cluster", "RADIO",
     "240 Mly. Its hot gas rings at a B-flat 57 octaves below middle C."),
    ("Coma Cluster", 12.9989, 27.9800, 0.02310, "cluster", "VISUAL",
     "320 Mly. Where Zwicky first noticed the galaxies moved far too fast for the visible mass."),
    ("Hercules Cluster", 16.0892, 17.7500, 0.03660, "cluster", "VISUAL",
     "500 Mly. Still assembling: galaxies here are visibly colliding."),
    ("Great Attractor", 16.3000, -60.0000, 0.01570, "structure", "RADIO",
     "220 Mly. A gravitational anomaly pulling our whole supercluster toward it."),
    ("Bootes Void", 14.8333, 46.0000, 0.05000, "structure", "VISUAL",
     "330 Mly across and almost entirely empty. The dial finds nothing here. That is the finding."),
    ("Sloan Great Wall", 10.9000, 7.0000, 0.07300, "structure", "VISUAL",
     "A filament of galaxies 1.4 billion ly long. Structure on a scale with no right to exist."),
    ("3C 273", 12.4853, 2.0524, 0.15834, "quasar", "RADIO",
     "The first object ever recognised as a quasar. 2.4 Gly, outshines its entire galaxy."),
    ("Markarian 421", 11.0744, 38.2088, 0.03000, "quasar", "RADIO",
     "A blazar: a relativistic jet pointed almost exactly at us."),
    ("FRB 121102", 5.5250, 33.1480, 0.19273, "exotic", "RADIO",
     "Repeating fast radio burst. Milliseconds long, 3 Gly away, cause still unsettled."),
    ("3C 48", 1.6286, 33.1597, 0.36700, "quasar", "RADIO",
     "4 Gly. For years its spectrum made no sense to anyone looking at it."),
    ("3C 279", 12.9364, -5.7894, 0.53620, "quasar", "RADIO",
     "5.5 Gly. Appears to eject material faster than light -- a projection effect."),
    ("PKS 1830-211", 18.5583, -21.0611, 2.50700, "quasar", "RADIO",
     "Gravitationally lensed into two images by a galaxy directly in the way."),
    ("ULAS J1120+0641", 11.3344, 6.6870, 7.08500, "quasar", "RADIO",
     "A billion-solar-mass black hole, 770 Myr after the Big Bang. Far too big, far too early."),
    ("GN-z11", 12.6106, 62.2428, 10.60000, "galaxy", "THERMAL",
     "Seen as it was 400 Myr after the Big Bang. Its light is stretched out of the optical entirely."),
    ("JADES-GS-z13-0", 3.5262, -27.8140, 13.20000, "galaxy", "THERMAL",
     "One of the earliest galaxies resolved. 330 Myr after the Big Bang."),
    ("Hubble Deep Field", 12.6122, 62.2200, 1.00000, "structure", "VISUAL",
     "A patch of apparently empty sky that turned out to contain thousands of galaxies."),
    ("Cosmic Microwave Background", 0.0000, 0.0000, 1089.00, "structure", "RADIO",
     "The surface of last scattering. 13.8 Gyr. Beyond this the universe is opaque."),
    ("M42 Orion Nebula", 5.5881, -5.3911, 0.0, "nebula", "THERMAL",
     "1,344 ly. An active stellar nursery, lit from inside by the Trapezium cluster."),
    ("Horsehead Nebula", 5.6836, -2.4581, 0.0, "nebula", "THERMAL",
     "Cold dust silhouetted against glowing hydrogen. Dark because it is opaque, not empty."),
    ("M1 Crab Nebula", 5.5755, 22.0145, 0.0, "remnant", "RADIO",
     "The wreck of a supernova seen from Earth in 1054 AD. A pulsar spins at its heart 30x a second."),
    ("Carina Nebula", 10.7517, -59.8678, 0.0, "nebula", "THERMAL",
     "7,500 ly and 460 ly across, containing several of the most massive stars known."),
    ("M8 Lagoon Nebula", 18.0603, -24.3867, 0.0, "nebula", "THERMAL",
     "An emission nebula with visible funnel-shaped tornadoes of hot gas."),
    ("M16 Eagle Nebula", 18.3129, -13.7917, 0.0, "nebula", "THERMAL",
     "Contains the Pillars of Creation: dust columns being eroded by nearby starlight."),
    ("M20 Trifid Nebula", 18.0450, -23.0300, 0.0, "nebula", "VISUAL",
     "Emission, reflection and dark nebula in one object, cut into three by dust lanes."),
    ("M57 Ring Nebula", 18.8933, 33.0292, 0.0, "nebula", "VISUAL",
     "A dying sun-like star's shed outer atmosphere, seen down the barrel."),
    ("M27 Dumbbell Nebula", 19.9936, 22.7211, 0.0, "nebula", "VISUAL",
     "The first planetary nebula ever discovered. 1,360 ly."),
    ("Helix Nebula", 22.4942, -20.8372, 0.0, "nebula", "VISUAL",
     "655 ly. Close enough that its radial dust knots resolve individually."),
    ("Cat's Eye Nebula", 17.9767, 66.6331, 0.0, "nebula", "VISUAL",
     "Eleven concentric shells, ejected in pulses roughly 1,500 years apart."),
    ("NGC 7000 North America", 20.9783, 44.3300, 0.0, "nebula", "THERMAL",
     "A vast, faint emission region shaped by dust into a recognisable coastline."),
    ("Veil Nebula", 20.7600, 30.7000, 0.0, "remnant", "VISUAL",
     "Filaments from a supernova 10,000-20,000 years ago, still expanding."),
    ("Cassiopeia A", 23.3911, 58.8150, 0.0, "remnant", "RADIO",
     "The brightest radio source outside the solar system."),
    ("Rosette Nebula", 6.5500, 4.9500, 0.0, "nebula", "THERMAL",
     "A ring of gas cleared out from the middle by the winds of the cluster inside it."),
    ("Tarantula Nebula", 5.6433, -69.1000, 0.00093, "nebula", "THERMAL",
     "In the LMC. If it were as close as Orion it would cast shadows on the ground."),
    ("M45 Pleiades", 3.7900, 24.1167, 0.0, "open", "VISUAL",
     "444 ly. Hot young stars still tangled in the dust they are passing through."),
    ("Hyades", 4.4500, 15.8700, 0.0, "open", "VISUAL",
     "153 ly. The nearest open cluster; Aldebaran is in front of it, not in it."),
    ("M44 Beehive", 8.6733, 19.6211, 0.0, "open", "VISUAL",
     "610 ly. Known as a 'little cloud' since antiquity, resolved into stars by Galileo."),
    ("Double Cluster", 2.3300, 57.1400, 0.0, "open", "VISUAL",
     "Two open clusters 7,500 ly away, physically associated and nearly the same age."),
    ("Omega Centauri", 13.4464, -47.4795, 0.0, "globular", "VISUAL",
     "10 million stars in a ball 150 ly across. Probably the stripped core of a small galaxy."),
    ("M13 Hercules Cluster", 16.6949, 36.4603, 0.0, "globular", "VISUAL",
     "25,000 ly. Target of the 1974 Arecibo message. It will arrive in 25,000 years."),
    ("47 Tucanae", 0.4014, -72.0808, 0.0, "globular", "VISUAL",
     "Second brightest globular, packed so tightly its core stars collide."),
    ("M15", 21.4996, 12.1670, 0.0, "globular", "VISUAL",
     "One of the densest known globulars -- the core has undergone collapse."),
    ("M22", 18.6064, -23.9047, 0.0, "globular", "VISUAL",
     "10,600 ly. Contains two candidate stellar-mass black holes."),
    ("Sagittarius A*", 17.7614, -29.0078, 0.0, "exotic", "RADIO",
     "The 4.3-million-solar-mass black hole at the centre of our galaxy. 26,000 ly."),
    ("Cygnus X-1", 19.9723, 35.2016, 0.0, "exotic", "RADIO",
     "A black hole pulling a stream of gas off a blue supergiant companion."),
    ("Vela Pulsar", 8.5835, -45.1765, 0.0, "exotic", "RADIO",
     "A neutron star rotating 11 times a second, left over from a supernova 11,000 years ago."),
    ("SS 433", 19.1965, 4.9828, 0.0, "exotic", "RADIO",
     "Fires two opposed jets at a quarter of light speed, precessing on a 162-day cycle."),
    ("PSR B1919+21", 19.3589, 21.8830, 0.0, "exotic", "RADIO",
     "The first pulsar found. Its discovery signal was catalogued LGM-1 before the cause was known."),
]


# ==========================================================================
# ANOMALIES
# ==========================================================================

ANOMALY_TYPES = [
    dict(kind="Repeating Signal", band="RADIO", trait="",
         classify="Structured pulse train. Interval constant to nine decimal places.",
         resolve="Pulse interval matches this array's own calibration cycle. The signal predates the array."),
    dict(kind="Gravitational Lensing Artifact", band="VISUAL", trait="",
         classify="Background sources smeared into arcs. Foreground mass unaccounted for.",
         resolve="Lens mass solved: 10^13 solar masses, no luminous counterpart. Dark matter halo, unambiguous."),
    dict(kind="Thermal Bloom", band="THERMAL", trait="",
         classify="Localised heat signature. No light source at this position on any other band.",
         resolve="Bloom is cooling on a blackbody curve, from an origin temperature of 4,400 K. Something was hot here recently."),
    dict(kind="Unidentified Silhouette", band="VISUAL", trait="flicker",
         classify="Solid returns radar but no spectrum. Outline is geometric.",
         resolve="Silhouette resolved: flat, bilaterally symmetric, 900 km across. It has an axis of symmetry. Nothing natural does."),
    dict(kind="Organic Spectral Trace", band="THERMAL", trait="shy",
         classify="Sensor reports complex carbon chains in hard vacuum. Recalibration does not clear it.",
         resolve="Chains re-read: chlorophyll-adjacent absorption at 680 nm. The array has no explanation and neither do you."),
    dict(kind="Temporal Echo", band="RADIO", trait="flicker",
         classify="Object registers at two positions, 6.1 seconds apart, converging.",
         resolve="Both returns are the same object. The lag matches signal round-trip to the array and back. It is echoing us."),
    dict(kind="Debris Field", band="THERMAL", trait="",
         classify="Fragmented material, tumbling, consistent with a destroyed structure.",
         resolve="Fragment census: 11,000 pieces, all reflective, all the same alloy. Reassembly volume estimated at 40 km."),
    dict(kind="Cold Spot", band="THERMAL", trait="",
         classify="Region 340 K below local background, with a hard edge.",
         resolve="Edge thickness under 2 km at this range. Thermal gradients do not terminate like that."),
    dict(kind="Resonant Hum", band="RADIO", trait="",
         classify="Subharmonic detected across the entire sensor band at once.",
         resolve="Frequency is 57 octaves below middle C -- identical to the Perseus Cluster's. Origin is not Perseus."),
    dict(kind="Observer Return", band="VISUAL", trait="edge",
         classify="Return signal briefly matches the profile of this array's own dish.",
         resolve="Return confirmed as a reflection of the array. Nothing at this position is reflective. Nothing is at this position."),
    dict(kind="Non-Sidereal Motion", band="VISUAL", trait="shy",
         classify="Contact holds position against the sky instead of drifting with it.",
         resolve="Track integrated over 6 hours: object is holding station relative to the array, not the stars. It is keeping up with us."),
    dict(kind="Blueshift Pocket", band="RADIO", trait="",
         classify="Local redshift reads negative in a region 3 arcmin across.",
         resolve="Pocket is approaching at 0.004c while its surroundings recede. It is moving through the expansion, not with it."),
    dict(kind="Radio Silence", band="RADIO", trait="edge",
         classify="Background radio drops to a true zero in a circular region. Not noise floor. Zero.",
         resolve="The region is not quiet. It is absorbing. The array has been transmitting into it for 40 minutes without noticing."),
    dict(kind="Duplicate Catalogue Entry", band="VISUAL", trait="flicker",
         classify="A catalogued star returns twice, offset by 2 arcsec, identical spectra.",
         resolve="Second entry has no parallax. It is not further away or nearer. It is not at a distance."),
    dict(kind="Recursive Structure", band="THERMAL", trait="",
         classify="Thermal map of the contact is self-similar at every zoom level tested.",
         resolve="Self-similarity holds to sensor resolution. Whatever is generating this is generating it deliberately."),
    dict(kind="Missing Occultation", band="VISUAL", trait="shy",
         classify="A background star dimmed. Nothing crossed in front of it.",
         resolve="Occultation profile implies an opaque body of 1,200 km at this range. The body returns no signal on any band."),
]

GLITCH_LINES = [
    "SIGNAL REALIGN...",
    "UNSCHEDULED PROCESS ACCESSING SENSOR ARRAY",
    "PACKET LOSS ON UPLINK -- RETRY 3/3",
    "ARRAY CLOCK DRIFT: +0.4s. CORRECTED.",
    "DISH SERVO REPORTS MOVEMENT. NO COMMAND ISSUED.",
    "CHANNEL 4 STATIC -- SOURCE UNRESOLVED",
    "CATALOGUE CHECKSUM MISMATCH ON 1 ENTRY. WHICH ONE IS NOT SPECIFIED.",
    "// no operator input for a while. still there?",
    "BACKGROUND SUBTRACTION FAILED. BACKGROUND IS NOT CONSTANT.",
    "RECEIVED: 0 BYTES. TIMESTAMP IS FOUR MINUTES AHEAD.",
]

VOICE_LINES = [
    "...say again...",
    "...still reading you...",
    "...is anyone...",
    "...not alone out...",
    "...keep the dish...",
    "...don't tune past...",
]

BOOT_LINES = [
    "VYSTLZ GROUND ARRAY  --  DEEP SKY RECEIVER  --  BIOS v3.0",
    "MEM CHECK ................ OK",
    "DISH SERVO ............... OK",
    "CRYO PREAMP .............. OK  (4.2 K)",
    "SENSOR BANK VIS/THM/RAD .. OK",
    "TOOL CAROUSEL ............ OK",
    "REDSHIFT TUNER ........... OK  (0 <= z <= 1089)",
    "CATALOGUE ................ LOADED",
    "TIME SYNC ................ OK",
    "",
    "> connect ground_array --observation-only",
    "> no survival subsystems present. nothing out here can reach you.",
    "> awaiting operator_",
]

HINTS = [
    "Objects answer on one band. If the ring crawls, try 1 / 2 / 3.",
    "The redshift dial (Q / E) is depth. z = 0 is the local sky.",
    "Anomalies need two scans. Come back a few hours later to resolve one.",
    "Scanning near the Sun is noisy. Work away from it.",
    "F cycles the log filter. Click a log entry to recentre on it.",
    "Hold SHIFT while panning with WASD to cross the sky faster.",
    "Some contacts are only there when you are not looking straight at them.",
    "R switches the crosshair to MONITOR mode -- lock a live graph on a contact.",
    "Scroll the mouse wheel over the Z dial for a fine trim.",
    "Tools 4-0 change what a scan finds. X opens the radial menu.",
    "A chevron on the edge of the sky means a tracked contact is off-screen.",
    "Variable stars dim on a schedule. Watch the red rings for dips.",
]

MILESTONES = [
    ("stars", 10, "10 stars catalogued."),
    ("stars", 50, "50 stars catalogued -- the local neighbourhood is taking shape."),
    ("stars", 150, "150 stars catalogued. No single ground observer ever logged this fast."),
    ("deep", 10, "10 deep-sky objects logged."),
    ("deep", 40, "40 deep-sky objects logged."),
    ("anom", 5, "5 anomalies classified."),
    ("anom", 20, "20 anomalies classified. The sky is answering back more than it should."),
    ("resolved", 5, "5 anomalies resolved."),
    ("resolved", 15, "15 anomalies resolved. Something out here keeps answering."),
    ("fixes", 3, "3 carrier recoveries. The array trusts you with the dish now."),
]


# ==========================================================================
# SECRET DEBUG / CHEAT MODES
# ==========================================================================
# VYSTLZ           -> debug panel (unlock after a short grace period)
# VYSTLZCMD        -> cheat panel
# Backtick         -> toggle whichever panel is unlocked

DEBUG_SEQ = [pygame.K_v, pygame.K_y, pygame.K_s, pygame.K_t, pygame.K_l, pygame.K_z]
CHEAT_SEQ = DEBUG_SEQ + [pygame.K_c, pygame.K_m, pygame.K_d]
DEBUG_KEY_WINDOW = 3.0    # keys must be typed within this window
DEBUG_FIRE_DELAY = 0.40   # wait this long after the final Z before firing debug

DEBUG_ACTIONS = [
    ("FORCE INTERFERENCE",              "interf_on"),
    ("CLEAR INTERFERENCE",              "interf_off"),
    ("FORCE LOG SPRAY (post-notice)",   "log_spray"),
    ("FORCE CALIB FIGHT (post-notice)", "calib_fight"),
    ("FORCE CRT GLITCH",                "glitch"),
    ("FORCE VOICE BURST",               "voice"),
    ("FORCE DUPLICATE STAR",            "dupe"),
    ("FORCE SECOND RETICLE",            "reticle"),
    ("SPAWN ANOMALY @ CURSOR",          "spawn_anom"),
    ("SPAWN CHAIN @ CURSOR",            "spawn_chain"),
    ("SPAWN T-D EVENT",                 "spawn_td"),
    ("NEXT T-D TYPE",                   "next_td"),
    ("FORCE DIMMING (RANDOM)",          "force_dim"),
    ("FORCE NOTICING EVENT",            "noticing"),
    ("FIRE NOTICING NOW",               "fire_noticing"),
    ("FORCE HORROR NOW",                "horror"),
    ("CLEAR NOTICING STATE",            "clear_noticing"),
    ("REVEAL ALL CONTACTS",             "reveal"),
    ("CATALOGUE NEARBY (20 deg)",       "scan_nearby"),
    ("RESOLVE ALL ANOMALIES",           "resolve_all"),
    ("+1000 SCORE",                     "score"),
    ("ADVANCE 6 GAME HOURS",            "advance"),
    ("UNLOCK FULL CODEX",               "unlock_codex"),
]

CHEAT_ACTIONS = [
    ("TOGGLE REVEAL ALL",         "c_reveal"),
    ("TOGGLE NO SOLAR NOISE",     "c_no_sol"),
    ("TOGGLE WIDE SCAN RADIUS",   "c_wide_scan"),
    ("TOGGLE FAST SCAN",          "c_fast"),
    ("TOGGLE INFINITE HOLD",      "c_inf_hold"),
    ("SET DIAL TO Z=1",           "c_z1"),
    ("SET DIAL TO Z=0.1",         "c_z01"),
    ("SET DIAL TO Z=0 (LOCAL)",   "c_z0"),
    ("ADVANCE 24 GAME HOURS",     "c_adv24"),
    ("ADVANCE 7 GAME DAYS",       "c_adv7d"),
    ("RESOLVE ALL ANOMALIES",     "c_resolve_all"),
    ("RESET ALL STAGES",          "c_reset_stages"),
    ("SPAWN ANOMALY @ CURSOR",    "c_spawn_anom"),
    ("SPAWN CHAIN @ CURSOR",      "c_spawn_chain"),
    ("KILL ALL TRANSIENTS",       "c_kill_transients"),
    ("+5000 SCORE",               "c_score"),
]


# ==========================================================================
# WORLD
# ==========================================================================

def gal_lat(ra_deg, dec_deg):
    ra = math.radians(ra_deg)
    dec = math.radians(dec_deg)
    ngp_ra = math.radians(192.8595)
    ngp_dec = math.radians(27.1284)
    s = (math.sin(dec) * math.sin(ngp_dec) +
         math.cos(dec) * math.cos(ngp_dec) * math.cos(ra - ngp_ra))
    return math.degrees(math.asin(max(-1.0, min(1.0, s))))


def designation(ra_deg, dec_deg, prefix="VDS"):
    h = ra_deg / 15.0
    hh = int(h)
    mm = int((h - hh) * 60)
    sign = "+" if dec_deg >= 0 else "-"
    ad = abs(dec_deg)
    dd = int(ad)
    dm = int((ad - dd) * 60)
    return "%s J%02d%02d%s%02d%02d" % (prefix, hh, mm, sign, dd, dm)


class SkyObject:
    __slots__ = ("oid", "name", "ra", "dec", "z", "kind", "band", "blurb", "mag",
                 "color", "dist_ly", "trait", "stage", "stage_time", "seed",
                 "variable", "dim_period", "dim_phase", "cause", "proc", "spawn",
                 "cluster_id", "note", "born", "chain")

    def __init__(self, oid, name, ra, dec, z, kind, band, blurb="", mag=6.0,
                 color=WHITE_STAR, dist_ly=None, trait="", proc=False):
        self.oid = oid
        self.name = name
        self.ra = ra % 360.0
        self.dec = max(-89.9, min(89.9, dec))
        self.z = z
        self.kind = kind
        self.band = band
        self.blurb = blurb
        self.mag = mag
        self.color = color
        self.dist_ly = dist_ly
        self.trait = trait
        self.stage = 0
        self.stage_time = 0.0
        self.seed = (oid * 2654435761) % 1000003
        self.variable = False
        self.dim_period = 0.0
        self.dim_phase = 0.0
        self.cause = None
        self.proc = proc
        self.spawn = False
        self.cluster_id = -1
        self.note = ""
        self.born = 0.0
        self.chain = False

    @property
    def is_anomaly(self):
        return self.kind == "anomaly"

    def distance_text(self):
        if self.dist_ly is not None:
            if self.dist_ly < 0.001:
                return "8.3 light-minutes"
            if self.dist_ly < 10000:
                return "%.2f ly" % self.dist_ly
            return "%.0f ly" % self.dist_ly
        if self.z <= 0.00001:
            return "local"
        mly = light_travel_mly(abs(self.z))
        if self.z < 0:
            return "%.2f Mly (approaching)" % mly
        if mly < 1000:
            return "%.1f Mly" % mly
        return "%.2f Gly" % (mly / 1000.0)

    def dim_amount(self, game_hours):
        if not self.variable:
            return 0.0
        phase = (game_hours + self.dim_phase) % self.dim_period
        w = self.dim_period * 0.16
        if phase < w:
            return math.sin(phase / w * math.pi) * 0.75
        return 0.0

    def is_dimmed(self, game_hours):
        return self.dim_amount(game_hours) > 0.25


GRID_DEG = 6.0


class World:
    def __init__(self, seed):
        self.seed = seed
        self.rng = random.Random(seed)
        self.objects = []
        self.by_id = {}
        self.grid = {}
        self.star_by_name = {}
        self.next_oid = 1
        self.attention = {}
        self._build()

    def _add(self, obj):
        self.objects.append(obj)
        self.by_id[obj.oid] = obj
        self._index(obj)
        return obj

    def _index(self, obj):
        key = (int(obj.ra // GRID_DEG), int((obj.dec + 90) // GRID_DEG))
        self.grid.setdefault(key, []).append(obj)

    def reindex(self):
        self.grid = {}
        for o in self.objects:
            self._index(o)

    def _oid(self):
        v = self.next_oid
        self.next_oid += 1
        return v

    def _build(self):
        rng = self.rng

        for name, ra_h, dec, dist, mag, sp in STARS_RAW:
            if name == "Sol":
                continue
            o = SkyObject(self._oid(), name, ra_h * 15.0, dec, 0.0, "star", "VISUAL",
                          mag=mag, color=spectral_color(sp), dist_ly=dist)
            o.note = sp
            if sp in ("M", "K") and mag < 4.0:
                o.band = "THERMAL"
            self._add(o)
            self.star_by_name[name] = o

        known_variable = ["Algol", "Mira", "Delta Cephei", "Betelgeuse", "Eta Carinae"]
        pool = [self.star_by_name[n] for n in known_variable if n in self.star_by_name]
        pool += rng.sample([o for o in self.objects if o.kind == "star" and o.mag < 3.5], 4)
        for s in pool:
            s.variable = True
            s.dim_period = rng.uniform(7.0, 26.0)
            s.dim_phase = rng.uniform(0, s.dim_period)
            s.cause = rng.choice(DIM_CAUSES)

        for name, ra_h, dec, z, kind, band, blurb in DEEP_SKY_RAW:
            o = SkyObject(self._oid(), name, ra_h * 15.0, dec, z, kind, band,
                          blurb=blurb, mag=8.0, color=self._kind_color(kind))
            self._add(o)

        made = 0
        while made < 3400:
            ra = rng.uniform(0, 360)
            dec = math.degrees(math.asin(rng.uniform(-1, 1)))
            b = abs(gal_lat(ra, dec))
            p = math.exp(-(b / 22.0) ** 2) * 0.88 + 0.12
            if rng.random() > p:
                continue
            made += 1
            sp = rng.choice("OBAFGKKMMM")
            mag = rng.uniform(4.2, 9.4)
            dist = 10 ** rng.uniform(1.4, 3.8)
            o = SkyObject(self._oid(), designation(ra, dec, "VDS"), ra, dec, 0.0,
                          "star", "THERMAL" if sp in "KM" else "VISUAL",
                          mag=mag, color=spectral_color(sp), dist_ly=dist, proc=True)
            o.note = sp
            self._add(o)

        clusters = []
        for ci in range(90):
            cz = math.exp(rng.uniform(math.log(0.004), math.log(2.4)))
            cra = rng.uniform(0, 360)
            cdec = math.degrees(math.asin(rng.uniform(-1, 1)))
            if abs(gal_lat(cra, cdec)) < 9 and rng.random() < 0.75:
                continue
            clusters.append((cra, cdec, cz, 2.2 + 9.0 / (1 + cz * 3)))
        for ci, (cra, cdec, cz, spread) in enumerate(clusters):
            n = rng.randint(6, 26)
            for _ in range(n):
                ra = cra + rng.gauss(0, spread) / max(0.2, math.cos(math.radians(cdec)))
                dec = cdec + rng.gauss(0, spread)
                if abs(dec) > 88:
                    continue
                z = max(0.0008, cz * (1 + rng.gauss(0, 0.012)))
                kind = "galaxy"
                band = "VISUAL" if z < 0.9 else "THERMAL"
                if rng.random() < 0.06:
                    kind, band = "quasar", "RADIO"
                o = SkyObject(self._oid(), designation(ra % 360, dec, "VDS"), ra, dec, z,
                              kind, band, mag=rng.uniform(13, 20),
                              color=self._kind_color(kind), proc=True)
                o.cluster_id = ci
                self._add(o)
        for _ in range(1500):
            ra = rng.uniform(0, 360)
            dec = math.degrees(math.asin(rng.uniform(-1, 1)))
            if abs(gal_lat(ra, dec)) < 8 and rng.random() < 0.8:
                continue
            z = math.exp(rng.uniform(math.log(0.003), math.log(6.0)))
            kind = "galaxy"
            band = "VISUAL" if z < 0.9 else "THERMAL"
            if rng.random() < 0.05:
                kind, band = "quasar", "RADIO"
            o = SkyObject(self._oid(), designation(ra, dec, "VDS"), ra, dec, z, kind, band,
                          mag=rng.uniform(14, 21), color=self._kind_color(kind), proc=True)
            self._add(o)

        anchors = [o for o in self.objects if not o.proc]
        for i in range(46):
            t = rng.choice(ANOMALY_TYPES)
            if rng.random() < 0.62 and anchors:
                host = rng.choice(anchors)
                ra = host.ra + rng.gauss(0, 1.4) / max(0.25, math.cos(math.radians(host.dec)))
                dec = host.dec + rng.gauss(0, 1.4)
                z = host.z
                near = host.name
            else:
                ra = rng.uniform(0, 360)
                dec = math.degrees(math.asin(rng.uniform(-1, 1)))
                z = 0.0 if rng.random() < 0.55 else math.exp(rng.uniform(math.log(0.005), math.log(1.6)))
                near = ""
            o = SkyObject(self._oid(), t["kind"], ra, dec, z, "anomaly", t["band"],
                          blurb=t["classify"], mag=9.0, color=AMBER, trait=t["trait"])
            o.note = near
            self._add(o)

        self.reindex()

    def _kind_color(self, kind):
        return {
            "galaxy": (206, 214, 255), "cluster": (190, 200, 250),
            "quasar": VIOLET, "nebula": (255, 150, 190), "globular": (255, 232, 190),
            "open": (200, 220, 255), "remnant": (170, 255, 220), "exotic": CYAN,
            "structure": (150, 170, 210), "anomaly": AMBER,
        }.get(kind, WHITE_STAR)

    def spawn_anomaly(self, ra, dec, z, game_hours, type_data=None, note="", chain=False):
        t = type_data or random.choice(ANOMALY_TYPES)
        o = SkyObject(self._oid(), t["kind"], ra, dec, z, "anomaly", t["band"],
                      blurb=t["classify"], mag=9.0, color=AMBER, trait=t["trait"])
        o.spawn = True
        o.born = game_hours
        o.note = note
        o.chain = chain
        self._add(o)
        return o

    def cell(self, ra, dec):
        return (int((ra % 360) // GRID_DEG), int((dec + 90) // GRID_DEG))

    def nearby(self, ra, dec, pad_cells=1):
        cx, cy = self.cell(ra, dec)
        out = []
        ncx = int(360 // GRID_DEG)
        for dx in range(-pad_cells, pad_cells + 1):
            for dy in range(-pad_cells, pad_cells + 1):
                out.extend(self.grid.get(((cx + dx) % ncx, cy + dy), ()))
        return out

    def visible_cells(self, ra0, ra1, dec0, dec1):
        ncx = int(360 // GRID_DEG)
        out = []
        cy0 = max(0, int((dec0 + 90) // GRID_DEG))
        cy1 = min(int(180 // GRID_DEG), int((dec1 + 90) // GRID_DEG))
        span = ra1 - ra0
        if span >= 360:
            xs = range(ncx)
        else:
            x0 = int(ra0 // GRID_DEG)
            n = int(span // GRID_DEG) + 2
            xs = [(x0 + i) % ncx for i in range(n)]
        for cx in xs:
            for cy in range(cy0, cy1 + 1):
                c = self.grid.get((cx, cy))
                if c:
                    out.append(c)
        return out


DIM_CAUSES = [
    "Eclipsing companion: dense, non-luminous, orbital period matches the dip exactly.",
    "Debris ring crossing the line of sight on a fixed cadence.",
    "Intrinsic pulsation -- the star itself is breathing, not being covered.",
    "Unresolved binary; the secondary is dark and passes in front every cycle.",
    "Occulting body resolves, briefly, into a symmetrical silhouette. Then the scan cuts out.",
    "Dust cloud in transit, opacity consistent with a protoplanetary disc seen edge-on.",
]


# ==========================================================================
# TIME-DOMAIN EVENTS
# ==========================================================================
# Each event: kind, window (in-game hours), band, log line, resolve line.
# dur == 0.0 means log-only -- GRB / FRB are over before you can point at them.

EVENT_TYPES = [
    dict(kind="Supernova", dur=72.0, band="VISUAL",
         log="SUPERNOVA: new point source in %s. Brightening over days.",
         resolve="Light curve matches a Type Ia. Peak absolute magnitude -19.3. Distance confirmed."),
    dict(kind="Tidal Disruption", dur=240.0, band="RADIO",
         log="TIDAL DISRUPTION: dormant nucleus in %s flaring. Multi-band rise.",
         resolve="Rise-and-plateau profile consistent with a stellar tidal disruption. Black hole mass ~10^7 M_sun."),
    dict(kind="Kilonova", dur=14.0, band="RADIO",
         log="KILONOVA candidate at %s. Extremely brief. Watch now.",
         resolve="Red kilonova afterglow. r-process signature. Two neutron stars. It is already over."),
    dict(kind="Microlensing", dur=120.0, band="VISUAL",
         log="MICROLENSING: %s brightening symmetrically. No proper motion.",
         resolve="Symmetric light curve, no colour change. A compact mass crossed the line of sight. It is gone."),
    dict(kind="Flare Star", dur=1.5, band="VISUAL",
         log="FLARE: %s kicked. Minutes long. Monitor if you are quick.",
         resolve="Impulsive flare, X-ray to radio. Red dwarf magnetic reconnection. It will do this again."),
    dict(kind="Pulsar Glitch", dur=48.0, band="RADIO",
         log="GLITCH: rotation discontinuity detected at %s.",
         resolve="Spin-up followed by slow recovery. Standard glitch signature. The star adjusted itself."),
    dict(kind="Fast Radio Burst", dur=0.0, band="RADIO",
         log="FRB: millisecond flash from %s. Afterglow may follow.",
         resolve="Dispersion measure consistent with an extragalactic origin. It repeated. That is the interesting part."),
    dict(kind="Gamma-Ray Burst", dur=0.0, band="RADIO",
         log="GRB AFTERGLOW in %s: peak was 4 hours ago. You missed it.",
         resolve="Relativistic jet, collimated. Standard long GRB. The peak lasted eleven seconds."),
]

# ==========================================================================
# CODEX
# ==========================================================================

CODEX_CELESTIAL = {
    "star":      "A self-luminous sphere of plasma held together by its own gravity. Most of the sky is this.",
    "galaxy":    "A gravitationally bound system of stars, gas, dust, and dark matter. Spiral, elliptical, or irregular.",
    "cluster":   "A gravitationally bound association of galaxies, from a handful of members to thousands.",
    "quasar":    "The active nucleus of a distant galaxy, powered by accretion onto a supermassive black hole.",
    "nebula":    "A cloud of interstellar gas and dust. Emission, reflection, or dark against what lies behind.",
    "globular":  "A tight spherical swarm of old stars orbiting the galactic halo.",
    "open":      "A loose association of young stars recently formed from the same molecular cloud.",
    "remnant":   "The expanding debris of a stellar explosion, with a compact object at its centre.",
    "exotic":    "Compact and relativistic systems: pulsars, black holes, relativistic jets.",
    "structure": "Large-scale cosmic features: filaments, voids, walls, the surface of last scattering.",
}

CODEX_ANOMALY = {
    "Repeating Signal":               "Structured emission at a fixed cadence. Origin unknown. The interval is the interesting part.",
    "Gravitational Lensing Artifact": "Background sources distorted into arcs. Foreground mass not accounted for by any visible object.",
    "Thermal Bloom":                  "Localised heat without an optical counterpart. Cools on a blackbody curve.",
    "Unidentified Silhouette":        "Solid return, no spectrum. Geometrically regular outline.",
    "Organic Spectral Trace":         "Complex carbon chemistry in hard vacuum. Does not clear on recalibration.",
    "Temporal Echo":                  "Two returns from the same position, separated in time.",
    "Debris Field":                   "Fragmented material, tumbling. Consistent with a destroyed structure.",
    "Cold Spot":                      "Region far below local background with a hard edge.",
    "Resonant Hum":                   "Subharmonic across the entire sensor band. Frequency resembles known cluster scales.",
    "Observer Return":                "Signal briefly matches the array's own transmission profile.",
    "Non-Sidereal Motion":            "Contact holds position against the sky. Not drifting with the stars.",
    "Blueshift Pocket":               "Local redshift reads negative in a small region.",
    "Radio Silence":                  "Background drops to true zero in a circular region. Not a noise floor.",
    "Duplicate Catalogue Entry":      "A catalogued object returns twice with identical spectra.",
    "Recursive Structure":            "Thermal map is self-similar at every zoom level tested.",
    "Missing Occultation":            "A star dimmed. Nothing crossed in front of it.",
}


# ==========================================================================
# AUDIO
# ==========================================================================

class Audio:
    def __init__(self):
        self.ok = False
        self.enabled = True
        self.master = 0.8
        if not HAVE_NUMPY:
            return
        try:
            pygame.mixer.pre_init(44100, -16, 2, 512)
            pygame.mixer.init()
            pygame.mixer.set_num_channels(16)
            self.rate = 44100
            self.ok = True
        except Exception:
            self.ok = False
            return

        self.s_tick = self._tone([520], 0.045, 0.10)
        self.s_lock = self._chord([660, 990, 1320], 0.22, 0.17)
        self.s_anom = self._chord([220, 440, 466], 0.40, 0.19)
        self.s_resolve = self._chord([330, 495, 660, 880], 0.55, 0.16)

        # pitched-down variant of the "log entry" chord. Only ever used
        # when something other than the operator is writing to the log.
        self.s_horror = self._chord([110, 165, 220], 1.60, 0.20)
        self.s_miss = self._tone([330, 247], 0.18, 0.055, fade=0.05)
        self.s_mode = self._tone([740], 0.05, 0.08)
        self.s_dial = self._tone([1200], 0.018, 0.045)
        self.s_glitch = self._noise(0.10, 0.16, harsh=True)
        self.s_deny = self._tone([180], 0.14, 0.09)
        self.s_ui = self._tone([880], 0.03, 0.06)
        self.voices = [self._voice(i) for i in range(4)]

        self.hum = self._hum(6.0, 0.055)
        self.static = self._noise_loop(3.0, 0.5)
        self.ch_hum = pygame.mixer.Channel(14)
        self.ch_static = pygame.mixer.Channel(15)
        self.ch_hum.play(self.hum, loops=-1)
        self.ch_static.play(self.static, loops=-1)
        self.ch_static.set_volume(0.0, 0.0)
        self.set_hum_pan(0.5, 1.0)

    def _stereo(self, mono):
        arr = np.repeat(mono.reshape(-1, 1), 2, axis=1)
        return pygame.sndarray.make_sound(np.ascontiguousarray(arr.astype(np.int16)))

    def _env(self, n, fade):
        env = np.ones(n)
        f = max(1, int(self.rate * fade))
        if f * 2 < n:
            env[:f] = np.linspace(0, 1, f)
            env[-f:] = np.linspace(1, 0, f)
        return env

    def _tone(self, freqs, dur, vol, fade=0.012):
        n = int(self.rate * dur)
        t = np.linspace(0, dur, n, False)
        wave = np.zeros(n)
        for i, f in enumerate(freqs):
            seg = np.zeros(n)
            a = int(n * i / len(freqs))
            b = int(n * (i + 1) / len(freqs))
            seg[a:b] = np.sin(f * 2 * np.pi * t[a:b])
            wave += seg
        data = wave * self._env(n, fade) * vol * 32767
        return self._stereo(data)

    def _chord(self, freqs, dur, vol):
        n = int(self.rate * dur)
        t = np.linspace(0, dur, n, False)
        wave = sum(np.sin(f * 2 * np.pi * t) for f in freqs) / len(freqs)
        env = np.linspace(1, 0, n) ** 0.7
        return self._stereo(wave * env * vol * 32767)

    def _noise(self, dur, vol, harsh=False):
        n = int(self.rate * dur)
        wave = np.random.uniform(-1, 1, n)
        if harsh:
            wave = np.sign(wave) * np.abs(wave) ** 0.5
        env = np.linspace(1, 0, n) ** 1.4
        return self._stereo(wave * env * vol * 32767)

    def _noise_loop(self, dur, vol):
        n = int(self.rate * dur)
        w = np.random.uniform(-1, 1, n)
        k = 12
        w = np.convolve(w, np.ones(k) / k, mode="same")
        w = w / (np.max(np.abs(w)) + 1e-9)
        return self._stereo(w * vol * 32767)

    def _hum(self, dur, vol):
        n = int(self.rate * dur)
        t = np.linspace(0, dur, n, False)
        wave = (np.sin(55 * 2 * np.pi * t) * 0.55 +
                np.sin(110.3 * 2 * np.pi * t) * 0.22 +
                np.sin(27.5 * 2 * np.pi * t) * 0.18 +
                np.random.uniform(-1, 1, n) * 0.02)
        return self._stereo(wave * vol * 32767)

    def _voice(self, idx):
        dur = 1.1 + idx * 0.13
        n = int(self.rate * dur)
        t = np.linspace(0, dur, n, False)
        f0 = 96 + idx * 11
        vib = 1 + 0.03 * np.sin(2 * np.pi * 4.5 * t)
        src = np.sign(np.sin(f0 * 2 * np.pi * t * vib)) * 0.5
        fa = 520 + 180 * np.sin(2 * np.pi * 0.7 * t)
        fb = 1180 + 420 * np.sin(2 * np.pi * 0.5 * t + 1.1)
        wave = src * (np.sin(2 * np.pi * fa * t) * 0.5 + np.sin(2 * np.pi * fb * t) * 0.3)
        wave += np.random.uniform(-1, 1, n) * 0.06
        env = np.clip(np.sin(np.pi * np.linspace(0, 1, n)) ** 1.6, 0, 1)
        return self._stereo(wave * env * 0.042 * 32767)

    def play(self, snd, vol=1.0, pan=0.5):
        if not (self.ok and self.enabled and snd):
            return
        try:
            ch = pygame.mixer.find_channel(True)
            if ch is None:
                return
            ch.set_volume(max(0.0, (1 - pan) * 2) * vol * self.master,
                          max(0.0, pan * 2) * vol * self.master)
            ch.play(snd)
        except Exception:
            pass

    def voice(self, pan=0.5):
        if self.ok and self.enabled and self.voices:
            self.play(random.choice(self.voices), vol=1.0, pan=pan)

    def set_hum_pan(self, pan, vol=1.0):
        if not self.ok:
            return
        v = 0.0 if not self.enabled else vol * self.master
        try:
            self.ch_hum.set_volume(min(1, (1 - pan) * 1.6) * v, min(1, pan * 1.6) * v)
        except Exception:
            pass

    def set_static(self, amount, pan=0.5):
        if not self.ok:
            return
        v = 0.0 if not self.enabled else amount * self.master
        try:
            self.ch_static.set_volume(min(1, (1 - pan) * 1.6) * v, min(1, pan * 1.6) * v)
        except Exception:
            pass

    def stop_all(self):
        if self.ok:
            try:
                pygame.mixer.stop()
            except Exception:
                pass


# ==========================================================================
# DRAW HELPERS
# ==========================================================================

def clamp(v, lo, hi):
    return lo if v < lo else (hi if v > hi else v)


def lerp(a, b, t):
    return a + (b - a) * t


def lerp_color(c1, c2, t):
    return (int(lerp(c1[0], c2[0], t)), int(lerp(c1[1], c2[1], t)), int(lerp(c1[2], c2[2], t)))


def dim_color(c, f):
    return (int(c[0] * f), int(c[1] * f), int(c[2] * f))


def bar_str(frac, width=8):
    frac = clamp(frac, 0.0, 1.0)
    n = int(round(frac * width))
    return "[" + "#" * n + "." * (width - n) + "]"


_GLOW_CACHE = {}


def glow_sprite(radius, color):
    r = max(1, int(radius))
    key = (r, color[0] // 16, color[1] // 16, color[2] // 16)
    s = _GLOW_CACHE.get(key)
    if s is not None:
        return s
    size = r * 6 + 4
    s = pygame.Surface((size, size), pygame.SRCALPHA)
    c = size // 2
    for i in range(6, 0, -1):
        rr = r * i * 0.5
        a = int(clamp(34 / i, 0, 255))
        pygame.draw.circle(s, (color[0], color[1], color[2], a), (c, c), int(rr))
    pygame.draw.circle(s, (min(255, color[0] + 40), min(255, color[1] + 40),
                           min(255, color[2] + 40), 255), (c, c), r)
    if len(_GLOW_CACHE) > 900:
        _GLOW_CACHE.clear()
    _GLOW_CACHE[key] = s
    return s


def blit_glow(surf, pos, radius, color):
    s = glow_sprite(radius, color)
    surf.blit(s, (pos[0] - s.get_width() // 2, pos[1] - s.get_height() // 2),
              special_flags=pygame.BLEND_RGBA_ADD)


def draw_diamond(surf, center, size, color, filled=False, width=2):
    x, y = center
    pts = [(x, y - size), (x + size, y), (x, y + size), (x - size, y)]
    pygame.draw.polygon(surf, color, pts, 0 if filled else width)


def draw_reticle(surf, center, radius, color, rot=0.0, gap=0.35, width=2):
    x, y = center
    for k in range(4):
        a0 = rot + k * (math.pi / 2) + gap
        a1 = rot + (k + 1) * (math.pi / 2) - gap
        pts = [(x + math.cos(lerp(a0, a1, i / 7.0)) * radius,
                y + math.sin(lerp(a0, a1, i / 7.0)) * radius) for i in range(8)]
        pygame.draw.lines(surf, color, False, pts, width)


def make_scanlines(w, h):
    s = pygame.Surface((w, h), pygame.SRCALPHA)
    for y in range(0, h, 2):
        pygame.draw.line(s, (0, 0, 0, 44), (0, y), (w, y))
    return s


def make_vignette(w, h):
    step = 8
    small = pygame.Surface((w // step + 2, h // step + 2), pygame.SRCALPHA)
    cx, cy = small.get_width() / 2, small.get_height() / 2
    maxd = math.hypot(cx, cy)
    for j in range(small.get_height()):
        for i in range(small.get_width()):
            d = math.hypot(i - cx, j - cy) / maxd
            small.set_at((i, j), (0, 0, 0, int(clamp((d - 0.42) * 230, 0, 200))))
    return pygame.transform.smoothscale(small, (w, h))


def make_noise_tiles(w, h, count=5):
    tiles = []
    for _ in range(count):
        s = pygame.Surface((w, h), pygame.SRCALPHA)
        if HAVE_NUMPY:
            n = np.random.randint(0, 255, (w // 2, h // 2)).astype(np.uint8)
            mask = (n > 238)
            rgb = np.zeros((w // 2, h // 2, 3), dtype=np.uint8)
            rgb[..., 0] = np.where(mask, n, 0)
            rgb[..., 1] = np.where(mask, n, 0)
            rgb[..., 2] = np.where(mask, n, 0)
            small = pygame.surfarray.make_surface(rgb)
            small.set_colorkey((0, 0, 0))
            small.set_alpha(34)
            s.blit(pygame.transform.scale(small, (w, h)), (0, 0))
        tiles.append(s)
    return tiles


def make_static_frames(w, h, count=4):
    frames = []
    for _ in range(count):
        s = pygame.Surface((w, h), pygame.SRCALPHA)
        if HAVE_NUMPY:
            n = np.random.randint(0, 160, (w // 3, h // 3)).astype(np.uint8)
            rgb = np.dstack([n // 3, n, (n * 0.7).astype(np.uint8)])
            small = pygame.surfarray.make_surface(rgb)
            small.set_alpha(120)
            s.blit(pygame.transform.scale(small, (w, h)), (0, 0))
            for _ in range(6):
                y = random.randint(0, h - 1)
                pygame.draw.rect(s, (200, 255, 230, 40), (0, y, w, random.randint(1, 5)))
        frames.append(s)
    return frames


def wrap_text(text, font, max_w, max_lines=99):
    words, lines, cur = text.split(" "), [], ""
    for wd in words:
        test = (cur + " " + wd).strip()
        if font.size(test)[0] > max_w and cur:
            lines.append(cur)
            cur = wd
            if len(lines) >= max_lines:
                return lines
        else:
            cur = test
    if cur:
        lines.append(cur)
    return lines[:max_lines]


def text_at(surf, font, s, pos, color, alpha=255, glow=True, align="left"):
    r = font.render(s, True, color)
    if alpha < 255:
        r.set_alpha(alpha)
    w, h = r.get_size()
    x, y = pos
    if align == "right":
        x -= w
    elif align == "center":
        x -= w // 2
    if glow:
        g = font.render(s, True, color)
        g.set_alpha(int(alpha * 0.30))
        surf.blit(g, (x + 1, y))
        surf.blit(g, (x - 1, y))
    surf.blit(r, (x, y))
    return pygame.Rect(x, y, w, h)


def panel_rect(surf, rect, border=PHOS_FAINT, fill=(0, 14, 11, 178), radius=3):
    s = pygame.Surface((rect.w, rect.h), pygame.SRCALPHA)
    pygame.draw.rect(s, fill, s.get_rect(), border_radius=radius)
    pygame.draw.rect(s, (border[0], border[1], border[2], 220), s.get_rect(), 1, border_radius=radius)
    surf.blit(s, rect.topleft)


# ==========================================================================
# LAYOUT
# ==========================================================================

def _adaptive_window_size(dw, dh):
    """Pick a window size that uses most of the available screen without
    spilling past OS chrome, and without ever exceeding the physical screen."""
    w = max(900, int(dw * 0.90))
    h = max(600, int(dh * 0.88))
    w = min(w, max(800, dw - 20))
    h = min(h, max(560, dh - 80))
    return w, h


class Layout:
    def __init__(self, w, h):
        self.recompute(w, h)

    def recompute(self, w, h):
        self.w, self.h = w, h
        self.scale = clamp(h / 760.0, 0.72, 2.6)
        self.top_h = int(40 * self.scale)
        self.bottom_h = int(92 * self.scale)
        self.panel_w = int(clamp(w * 0.24, 240, 620))
        self.panel_open = True
        self.sky = pygame.Rect(0, self.top_h, w, h - self.top_h - self.bottom_h)
        self.panel = pygame.Rect(w - self.panel_w - 8, self.top_h + 8,
                                 self.panel_w, h - self.top_h - self.bottom_h - 16)
        self.bottom = pygame.Rect(0, h - self.bottom_h, w, self.bottom_h)


def load_fonts(scale):
    name = pygame.font.match_font(FONT_CANDIDATES) or None

    def mk(size, bold=False):
        f = pygame.font.Font(name, max(9, int(size * scale)))
        f.set_bold(bold)
        return f

    return {"xs": mk(12), "sm": mk(14), "md": mk(17), "lg": mk(22),
            "xl": mk(34, True), "title": mk(52, True)}


# ==========================================================================
# LOG
# ==========================================================================

CAT_ALL, CAT_STAR, CAT_ANOM, CAT_SYS = "ALL", "STARS", "ANOMALIES", "SYSTEM"
FILTERS = [CAT_ALL, CAT_STAR, CAT_ANOM, CAT_SYS]


class LogEntry:
    __slots__ = ("stamp", "text", "color", "cat", "oid")

    def __init__(self, stamp, text, color, cat, oid=None):
        self.stamp, self.text, self.color, self.cat, self.oid = stamp, text, color, cat, oid


# ==========================================================================
# GAME
# ==========================================================================

class Game:
    def __init__(self):
        pygame.init()
        pygame.display.set_caption(TITLE)
        _build_cosmology_tables()

        info = pygame.display.Info()
        dw, dh = info.current_w, info.current_h
        w, h = _adaptive_window_size(dw, dh)
        global SW, SH
        SW, SH = w, h
        self.fullscreen = False
        self.screen = pygame.display.set_mode((w, h), pygame.RESIZABLE | pygame.DOUBLEBUF)
        self.clock = pygame.time.Clock()

        self.L = Layout(w, h)
        self.fonts = load_fonts(self.L.scale)
        self.audio = Audio()
        self.rebuild_fx()

        self.shift = 0.0

        self.state = "MENU"
        self.menu_page = "MAIN"
        self.menu_sel = 0
        self.menu_msg = ""
        self.menu_msg_t = 0.0
        self.menu_t = 0.0
        self.buttons = []
        self.running = True
        self.settings = {"crt": True, "audio": True, "hints": True}
        self.world = None
        self.quick_slot = 1
        os.makedirs(SAVE_DIR, exist_ok=True)
        self.menu_stars = [(random.uniform(0, 1), random.uniform(0, 1),
                            random.uniform(0.2, 1.0), random.uniform(0, 6.28)) for _ in range(260)]

        # --- debug / cheat state -----------------------------------------
        self.debug_unlocked = False
        self.debug_open = False
        self.debug_keybuf = []
        self.debug_reveal = False
        self.debug_rects = []
        self.pending_debug_t = 0.0
        self.cheat_unlocked = False
        self.cheat_open = False
        self.cheat_rects = []
        # cheat flags
        self.cheat_no_solar = False
        self.cheat_wide_scan = False
        self.cheat_fast_scan = False
        self.cheat_inf_hold = False

        # --- last_slot for auto-save on notice arm ----------------------
        self.last_slot = None

        # --- defaults for attributes normally set by new_session() ------
        # render_crt() and the event handlers can run from the main menu
        # before any session exists, so these must always be present.
        self.horror_t = -1.0
        self.notice_reveal_t = -1.0
        self.notice_approach_t = -1.0
        self.notice_approach_start = None
        self.notice_target_oid = None
        self.finder_open = False
        self.radial_open = False
        self.radial_sel = 0
        self.interference = False
        self.sol_noise = 0.0
        self.panning = False
        self.dial_drag = False
        self.glitch_flash = 0.0
        self.fx_i = 0.0
        self.seed = 0
        self.cam_ra = 0.0
        self.cam_dec = 0.0
        self.zoom = 9.0
        self.z_dial = 0.0
        self.dial_p = 0.0
        self.mode = "VISUAL"
        self.tool = None
        self.game_hours = 6.0
        self.score = 0
        self.log = []
        self.filter_i = 0
        self.tab = 0
        self.help_page = 0
        self.milestones_done = set()
        self.stats = {"stars": 0, "deep": 0, "anom": 0, "resolved": 0, "fixes": 0}
        self.dim_markers = []
        self.chain_markers = []
        self.norm_anoms_scanned = 0
        self.chain_anoms_scanned = 0
        self.noticing_stage = 0
        self.noticing_oid = None
        self.monitors = []
        self.transients = []
        self.dupe = None
        self.toast = ""
        self.toast_t = 0.0
        self.visible_count = 0
        self.session_t = 0.0
        self.dial_center = (0, 0)
        self.dial_R = 1
        self.dial_rect = pygame.Rect(0, 0, 1, 1)
        self.mode_rects = []
        self.tool_rects = []
        self.tab_rects = []
        self.log_rects = []
        self.calib_rects = []
        self.help_nav_rects = []
        self.filter_rect = None
        self.pause_page = "MAIN"
        self.calib = None
        self.target = None

        # --- v3.1 aftermath state ---
        self.post_noticing_interf = 0     # 0 none, 1 red spray, 2 fight
        self.second_reticle = None
        self.second_reticle_cd = 0.0
        self.active_events = []
        self.debug_td_idx = 0
        self.codex_open = False
        self.codex_tab = 0
        self.codex_scroll = 0
        self.codex_seen = set()
        self.codex_rects = []

    # ----------------------------------------------------------------- setup
    def rebuild_fx(self):
        w, h = self.L.w, self.L.h
        self.scanlines = make_scanlines(w, h)
        self.vignette = make_vignette(w, h)
        self.noise_tiles = make_noise_tiles(w, h, 5)
        self.static_frames = make_static_frames(w, h, 4)
        self.fx_i = 0.0

    def on_resize(self, w, h):
        global SW, SH
        w, h = max(900, w), max(600, h)
        SW, SH = w, h
        self.screen = pygame.display.set_mode((w, h), pygame.RESIZABLE | pygame.DOUBLEBUF)
        self.L.recompute(w, h)
        self.fonts = load_fonts(self.L.scale)
        self.rebuild_fx()

    def toggle_fullscreen(self):
        self.fullscreen = not self.fullscreen
        if self.fullscreen:
            info = pygame.display.Info()
            self.screen = pygame.display.set_mode((0, 0), pygame.FULLSCREEN | pygame.DOUBLEBUF)
            w, h = self.screen.get_size()
        else:
            info = pygame.display.Info()
            w, h = _adaptive_window_size(info.current_w, info.current_h)
            self.screen = pygame.display.set_mode((w, h), pygame.RESIZABLE | pygame.DOUBLEBUF)
        global SW, SH
        SW, SH = w, h
        self.L.recompute(w, h)
        self.fonts = load_fonts(self.L.scale)
        self.rebuild_fx()

    # ------------------------------------------------------------ new / save
    def new_session(self, seed=None):
        seed = seed if seed is not None else random.randint(1, 10 ** 9)
        self.seed = seed
        self.world = World(seed)

        self.cam_ra = random.uniform(0.0, 360.0)
        self.cam_dec = random.uniform(-58.0, 58.0)
        self.zoom = random.uniform(7.5, 11.5)
        self.z_dial = 0.0
        self.dial_p = 0.0
        self.mode = "VISUAL"
        self.tool = None
        self.game_hours = 6.0
        self.score = 0
        self.log = []
        self.filter_i = 0
        self.tab = 0
        self.help_page = 0
        self.scan_p = 0.0
        self.scan_need = 1.0
        self.target = None
        self.hold_pos = None
        self.tick_notch = -1
        self.spectrum_phase = 0.0
        self.last_miss = None
        self.miss_cd = 0.0
        self.session_t = 0.0

        self.interference = False
        self.interf_t = 0.0
        self.calib = None
        self.next_interf = random.uniform(240, 420)

        self.glitch_cd = random.uniform(20, 45)
        self.glitch_flash = 0.0
        self.shift = 0.0

        self.monitor_mode = False
        self.monitors = []
        self.mon_target = None
        self.mon_scan_p = 0.0
        self.mon_hold_pos = None
        self.mon_need = 0.6

        self.dial_center = (0, 0)
        self.dial_R = 1

        self.milestones_done = set()

        self.dupe = None
        self.dupe_cd = random.uniform(120, 260)
        self.voice_cd = random.uniform(150, 400)
        self.transient_cd = random.uniform(70, 140)
        self.transients = []
        self.hint_i = 0
        self.hint_t = 0.0
        self.toast = ""
        self.toast_t = 0.0

        self.stats = {"stars": 0, "deep": 0, "anom": 0, "resolved": 0, "fixes": 0}

        # --- v3 systems ------------------------------------------------
        self.dim_markers = []
        self.chain_markers = []
        self.norm_anoms_scanned = 0
        self.chain_anoms_scanned = 0
        self.noticing_stage = 0
        self.noticing_oid = None
        self.horror_t = -1.0
        self.notice_reveal_t = -1.0
        self.notice_approach_t = -1.0
        self.notice_approach_start = None
        self.notice_target_oid = None
        self.finder_open = False
        self.radial_open = False
        self.radial_sel = 0

        self.last_slot = None
        self.dial_rect = pygame.Rect(0, 0, 1, 1)
        self.post_noticing_interf = 0
        self.second_reticle = None
        self.second_reticle_cd = random.uniform(60.0, 150.0)
        self.active_events = []
        self.codex_open = False
        self.codex_tab = 0
        self.codex_scroll = 0
        self.codex_seen = set()
        self.codex_rects = []
        self.mode_rects = []
        self.tool_rects = []
        self.tab_rects = []
        self.log_rects = []
        self.calib_rects = []
        self.filter_rect = None
        self.help_nav_rects = []
        self.panning = False
        self.dial_drag = False
        self.pause_page = "MAIN"
        self.sol_noise = 0.0
        self.visible_count = 0

        self.state = "BOOT"
        self.boot_t = 0.0
        self.log_add("SESSION START -- observation only. no survival subsystems present.",
                     PHOS_DIM, CAT_SYS)
        self.log_add("Array online. Redshift tuner at z = 0.000. Sensor: VISUAL. Tool: none.",
                     PHOS_DIM, CAT_SYS)

    # ---- serialisation ----------------------------------------------------
    def save_path(self, slot):
        return os.path.join(SAVE_DIR, "slot%d.json" % slot)

    def save_meta(self, slot):
        p = self.save_path(slot)
        if not os.path.exists(p):
            return None
        try:
            with open(p) as f:
                d = json.load(f)
            return {"score": d.get("score", 0), "hours": d.get("game_hours", 0),
                    "saved": d.get("saved_at", "?"), "stats": d.get("stats", {})}
        except Exception:
            return None

    def save_game(self, slot):
        try:
            states = {}
            for o in self.world.objects:
                if o.stage or o.spawn:
                    states[str(o.oid)] = [o.stage, round(o.stage_time, 3)]
            spawned = [[o.oid, o.name, round(o.ra, 5), round(o.dec, 5), o.z, o.band,
                        o.trait, o.blurb, o.note, round(o.born, 3), 1 if o.chain else 0]
                       for o in self.world.objects if o.spawn]
            data = {
                "version": VERSION,
                "seed": self.seed,
                "saved_at": datetime.datetime.now().strftime("%Y-%m-%d %H:%M"),
                "game_hours": self.game_hours,
                "score": self.score,
                "cam": [self.cam_ra, self.cam_dec, self.zoom],
                "dial_p": self.dial_p,
                "mode": self.mode,
                "tool": self.tool,
                "stats": self.stats,
                "settings": self.settings,
                "attention": {"%d,%d" % k: v for k, v in self.world.attention.items()},
                "states": states,
                "spawned": spawned,
                "next_oid": self.world.next_oid,
                "log": [[e.stamp, e.text, list(e.color), e.cat, e.oid] for e in self.log[-120:]],
                "milestones": list(self.milestones_done),
                "norm_anoms_scanned": self.norm_anoms_scanned,
                "chain_anoms_scanned": self.chain_anoms_scanned,
                "noticing_stage": self.noticing_stage,
                "noticing_oid": self.noticing_oid,
                "post_noticing_interf": self.post_noticing_interf,
                "codex_seen": sorted(self.codex_seen),
                "active_events": [[e["oid"], e["kind"], e["dur"], e["born"],
                                   e["band"], e["resolve"], e["log"]]
                                  for e in self.active_events],
            }
            with open(self.save_path(slot), "w") as f:
                json.dump(data, f)
            self.toast = "SAVED TO SLOT %d" % slot
            self.toast_t = 2.6
            return True
        except Exception as ex:
            self.toast = "SAVE FAILED: %s" % ex
            self.toast_t = 3.5
            return False

    def load_game(self, slot):
        p = self.save_path(slot)
        if not os.path.exists(p):
            return False
        try:
            with open(p) as f:
                d = json.load(f)
            self.new_session(d["seed"])
            self.game_hours = d.get("game_hours", 6.0)
            self.score = d.get("score", 0)
            cam = d.get("cam", [83, 0, 9])
            self.cam_ra, self.cam_dec, self.zoom = cam[0], cam[1], cam[2]
            self.dial_p = d.get("dial_p", 0.0)
            self.z_dial = self.p_to_z(self.dial_p)
            self.mode = d.get("mode", "VISUAL")
            self.tool = d.get("tool", None)
            self.stats.update(d.get("stats", {}))
            self.settings.update(d.get("settings", {}))
            self.audio.enabled = self.settings.get("audio", True)
            self.world.next_oid = d.get("next_oid", self.world.next_oid)
            for k, v in d.get("attention", {}).items():
                a, b = k.split(",")
                self.world.attention[(int(a), int(b))] = v
            for row in d.get("spawned", []):
                if len(row) == 11:
                    oid, name, ra, dec, z, band, trait, blurb, note, born, chain_flag = row
                else:
                    oid, name, ra, dec, z, band, trait, blurb, note, born = row
                    chain_flag = 0
                o = SkyObject(oid, name, ra, dec, z, "anomaly", band, blurb=blurb,
                              mag=9.0, color=AMBER, trait=trait)
                o.spawn, o.note, o.born = True, note, born
                o.chain = bool(chain_flag)
                self.world.objects.append(o)
                self.world.by_id[oid] = o
                self.world._index(o)
            for k, v in d.get("states", {}).items():
                o = self.world.by_id.get(int(k))
                if o:
                    o.stage, o.stage_time = v[0], v[1]
            self.log = [LogEntry(e[0], e[1], tuple(e[2]), e[3], e[4]) for e in d.get("log", [])]
            self.milestones_done = set(d.get("milestones", []))
            self.norm_anoms_scanned = d.get("norm_anoms_scanned", 0)
            self.chain_anoms_scanned = d.get("chain_anoms_scanned", 0)
            self.noticing_stage = d.get("noticing_stage", 0)
            self.noticing_oid = d.get("noticing_oid", None)
            self.post_noticing_interf = d.get("post_noticing_interf", 0)
            self.codex_seen = set(d.get("codex_seen", []))
            for row in d.get("active_events", []):
                oid, kind, dur, born, band, resolve, log = row
                self.active_events.append({"oid": oid, "kind": kind,
                                           "dur": dur, "born": born,
                                           "band": band, "resolve": resolve,
                                           "log": log})
            self.last_slot = slot
            self.state = "PLAY"
            self.toast = "SLOT %d LOADED" % slot
            self.toast_t = 2.6

            if self.noticing_stage == 1 and self.noticing_oid is not None:
                self.begin_notice_approach()
            return True
        except Exception as ex:
            self.menu_msg = "LOAD FAILED: %s" % ex
            self.menu_msg_t = 4.0
            return False

    # ----------------------------------------------------------------- utils
    def log_add(self, text, color=PHOS, cat=CAT_SYS, oid=None):
        self.log.append(LogEntry(self.clock_str(True), text, color, cat, oid))
        if len(self.log) > 400:
            self.log = self.log[-400:]

    def clock_str(self, short=False):
        tm = self.game_hours * 60.0
        day = int(tm // 1440) + 1
        hh, mm = int((tm // 60) % 24), int(tm % 60)
        if short:
            return "D%02d %02d:%02d" % (day, hh, mm)
        return "DAY %03d   %02d:%02d GST" % (day, hh, mm)

    def p_to_z(self, p):
        return (1090.0 ** clamp(p, 0, 1)) - 1.0

    def z_to_p(self, z):
        return math.log(max(0.0, z) + 1.0) / math.log(1090.0)

    def sun_pos(self):
        day = self.game_hours / 24.0
        lam = math.radians((day / 365.25) * 360.0 % 360.0)
        eps = math.radians(23.44)
        ra = math.degrees(math.atan2(math.cos(eps) * math.sin(lam), math.cos(lam))) % 360
        dec = math.degrees(math.asin(math.sin(eps) * math.sin(lam)))
        return ra, dec

    def ang_sep(self, ra1, dec1, ra2, dec2):
        p1, p2 = math.radians(dec1), math.radians(dec2)
        dl = math.radians(ra1 - ra2)
        v = math.sin(p1) * math.sin(p2) + math.cos(p1) * math.cos(p2) * math.cos(dl)
        return math.degrees(math.acos(clamp(v, -1, 1)))

    # ---- projection -------------------------------------------------------
    def world_to_screen(self, ra, dec):
        dra = (ra - self.cam_ra + 180.0) % 360.0 - 180.0
        k = math.cos(math.radians(self.cam_dec))
        x = self.L.w * 0.5 + dra * self.zoom * k
        y = self.L.sky.centery - (dec - self.cam_dec) * self.zoom
        return x, y

    def screen_to_world(self, x, y):
        k = max(0.08, math.cos(math.radians(self.cam_dec)))
        ra = self.cam_ra + (x - self.L.w * 0.5) / (self.zoom * k)
        dec = self.cam_dec - (y - self.L.sky.centery) / self.zoom
        return ra % 360.0, clamp(dec, -89.9, 89.9)

    # ---- band / visibility ------------------------------------------------
    def band_strength(self, obj):
        if abs(obj.z) < 1e-6:
            local = math.exp(-(self.dial_p / 0.035) ** 2)
            return local * 0.94 + (0.06 if obj.kind == "anomaly" else 0.0)
        lo = math.log(1.0 + max(obj.z, -0.0009))
        ld = math.log(1.0 + max(self.z_dial, 0.0))
        sigma = 0.05 + 0.02 * ld
        s = math.exp(-((lo - ld) / sigma) ** 2)
        if obj.kind == "anomaly":
            s = max(s, 0.06)
        return s

    def mode_match(self, obj):
        return obj.band == self.mode

    def solar_noise(self, ra, dec):
        if self.cheat_no_solar:
            return 0.0
        sra, sdec = self.sun_pos()
        sep = self.ang_sep(ra, dec, sra, sdec)
        if sep > 26.0:
            return 0.0
        return clamp((26.0 - sep) / 26.0, 0, 1) ** 1.5

    # ================================================================== LOOP
    def run(self):
        try:
            while self.running:
                dt = min(self.clock.tick(FPS) / 1000.0, 0.05)
                self.handle_events(dt)
                if self.state == "MENU":
                    self.menu_t += dt
                    self.menu_msg_t = max(0, self.menu_msg_t - dt)
                elif self.state == "BOOT":
                    self.boot_t += dt
                    if self.boot_t > len(BOOT_LINES) * 0.16 + 1.1:
                        self.state = "PLAY"
                elif self.state == "PLAY":
                    self.update(dt)
                elif self.state == "HORROR":
                    self.update_horror(dt)
                self.render()
        except BaseException:
            try:
                if (self.world is not None
                        and self.last_slot is not None
                        and self.state in ("PLAY", "PAUSE", "HORROR")):
                    self.save_game(self.last_slot)
            except Exception:
                pass
            raise
        finally:
            self.audio.stop_all()
            try:
                pygame.quit()
            except Exception:
                pass

    # ------------------------------------------------------------- input
    def handle_events(self, dt):
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                self.running = False
            elif e.type == pygame.VIDEORESIZE and not self.fullscreen:
                self.on_resize(e.w, e.h)
            elif e.type == pygame.KEYDOWN:
                self.on_key(e)
            elif e.type == pygame.MOUSEBUTTONDOWN:
                self.on_click(e)
            elif e.type == pygame.MOUSEBUTTONUP:
                if e.button == 2:
                    self.panning = False
                self.dial_drag = False
            elif e.type == pygame.MOUSEMOTION:
                self.on_motion(e)
            elif e.type == pygame.MOUSEWHEEL and self.state == "PLAY" \
                    and self.notice_approach_t < 0.0:
                if self.codex_open:
                    self.codex_scroll = max(0, self.codex_scroll - e.y)
                else:
                    mx, my = pygame.mouse.get_pos()
                    if self.dial_hit((mx, my)):
                        self.dial_p = clamp(self.dial_p + e.y * 0.01, 0, 1)
                        self.z_dial = self.p_to_z(self.dial_p)
                        self.audio.play(self.audio.s_dial, 0.3)
                    elif self.L.sky.collidepoint(mx, my):
                        self.zoom_at((mx, my), 1.16 ** e.y)

    def on_key(self, e):
        if getattr(self, "notice_approach_t", -1.0) >= 0.0:
            return
        k = e.key

        # --- capture keypresses for the debug/cheat sequences ---
        now = time.time()
        self.debug_keybuf.append((k, now))
        self.debug_keybuf = [(kk, tt) for kk, tt in self.debug_keybuf
                             if now - tt < DEBUG_KEY_WINDOW]
        if len(self.debug_keybuf) > 12:
            self.debug_keybuf = self.debug_keybuf[-12:]

        if len(self.debug_keybuf) >= len(CHEAT_SEQ):
            last9 = [x[0] for x in self.debug_keybuf[-len(CHEAT_SEQ):]]
            if last9 == CHEAT_SEQ:
                self.debug_keybuf = []
                self.pending_debug_t = 0.0
                self.cheat_rects = []
                if not self.cheat_unlocked:
                    self.cheat_unlocked = True
                    self.cheat_open = True
                    self.audio.play(self.audio.s_resolve, 1.0)
                    if getattr(self, "log", None) is not None:
                        self.log_add("CHEAT MODE UNLOCKED -- ` toggles", RED_WARN, CAT_SYS)
                    self.toast = "CHEAT MODE UNLOCKED"
                    self.toast_t = 3.0
                else:
                    self.cheat_open = not self.cheat_open
                return

        if len(self.debug_keybuf) >= len(DEBUG_SEQ):
            last6 = [x[0] for x in self.debug_keybuf[-len(DEBUG_SEQ):]]
            if last6 == DEBUG_SEQ:
                if self.pending_debug_t == 0.0:
                    self.pending_debug_t = now

        if k == pygame.K_BACKQUOTE:
            if self.cheat_unlocked:
                self.cheat_open = not self.cheat_open
                self.cheat_rects = []
                return
            if self.debug_unlocked:
                self.debug_open = not self.debug_open
                self.debug_rects = []
                return

        if self.state == "MENU":
            if k == pygame.K_ESCAPE:
                if self.menu_page == "MAIN":
                    self.running = False
                else:
                    self.menu_page = "MAIN"
            elif k == pygame.K_F11:
                self.toggle_fullscreen()
            return
        if self.state == "BOOT":
            if k in (pygame.K_SPACE, pygame.K_RETURN, pygame.K_ESCAPE):
                self.state = "PLAY"
            return
        if self.state == "HORROR":
            return
        if self.state == "PAUSE":
            if k in (pygame.K_ESCAPE, pygame.K_m):
                self.state = "PLAY"
            elif k == pygame.K_F11:
                self.toggle_fullscreen()
            return

        # ---- PLAY ----
        if self.codex_open:
            if k in (pygame.K_ESCAPE, pygame.K_k):
                self.codex_open = False
            elif k == pygame.K_LEFT:
                self.codex_tab = (self.codex_tab - 1) % 2
                self.codex_scroll = 0
            elif k == pygame.K_RIGHT:
                self.codex_tab = (self.codex_tab + 1) % 2
                self.codex_scroll = 0
            elif k == pygame.K_UP:
                self.codex_scroll = max(0, self.codex_scroll - 1)
            elif k == pygame.K_DOWN:
                self.codex_scroll = self.codex_scroll + 1
            return

        if self.finder_open:
            if k in (pygame.K_ESCAPE, pygame.K_0):
                self.finder_open = False
            return

        if k in (pygame.K_ESCAPE, pygame.K_m):
            self.state = "PAUSE"
            self.pause_page = "MAIN"
        elif k == pygame.K_F11:
            self.toggle_fullscreen()
        elif k == pygame.K_TAB:
            self.tab = (self.tab + 1) % 4
            self.audio.play(self.audio.s_ui, 0.5)
            if self.interference and self.tab == 2 and self.calib is None:
                self.start_calibration()
        elif k == pygame.K_f:
            self.filter_i = (self.filter_i + 1) % len(FILTERS)
        elif k == pygame.K_r:
            self.monitor_mode = not self.monitor_mode
            self.mon_target = None
            self.mon_scan_p = 0.0
            self.mon_hold_pos = None
            self.target = None
            self.scan_p = 0.0
            self.hold_pos = None
            self.audio.play(self.audio.s_mode, 0.7)
            self.toast = "MONITOR SCAN ON" if self.monitor_mode else "MONITOR SCAN OFF"
            self.toast_t = 2.0
        elif k == pygame.K_h:
            self.L.panel_open = not self.L.panel_open
        elif k in (pygame.K_1, pygame.K_2, pygame.K_3):
            self.mode = MODES[k - pygame.K_1]
            self.audio.play(self.audio.s_mode, 0.7)
            self.scan_p = 0.0
        elif k in TOOL_KEYS:
            t = TOOL_KEYS[k]
            self.tool = None if self.tool == t else t
            self.audio.play(self.audio.s_mode, 0.7)
            self.toast = "TOOL: %s" % (self.tool or "none")
            self.toast_t = 1.6
        elif k == pygame.K_0:
            self.finder_open = True
            self.audio.play(self.audio.s_ui, 0.6)
        elif k == pygame.K_k:
            self.codex_open = True
            self.codex_tab = 0
            self.codex_scroll = 0
            self.audio.play(self.audio.s_ui, 0.6)
        elif k == pygame.K_z:
            self.dial_p = 0.0
            self.z_dial = 0.0
            self.log_add("Tuner reset. z = 0.000 -- local sky.", PHOS_DIM, CAT_SYS)
        elif k == pygame.K_F5:
            self.save_game(self.quick_slot)
        elif k == pygame.K_F9:
            self.load_game(self.quick_slot)
        elif self.tab == 3 and k in (pygame.K_LEFT, pygame.K_RIGHT):
            if k == pygame.K_LEFT:
                self.help_page = (self.help_page - 1) % 4
            else:
                self.help_page = (self.help_page + 1) % 4
            self.audio.play(self.audio.s_ui, 0.5)
        elif self.tab == 2 and self.calib:
            self.calib_key(k)

    def on_motion(self, e):
        if self.state != "PLAY":
            return
        if getattr(self, "notice_approach_t", -1.0) >= 0.0:
            return
        if getattr(self, "panning", False):
            k = max(0.08, math.cos(math.radians(self.cam_dec)))
            self.cam_ra = (self.cam_ra - e.rel[0] / (self.zoom * k)) % 360
            self.cam_dec = clamp(self.cam_dec + e.rel[1] / self.zoom, -89, 89)
        if getattr(self, "dial_drag", False):
            self.dial_from_mouse(e.pos)

    def on_click(self, e):
        if self.state == "MENU":
            self.menu_click(e)
            return
        if self.state == "BOOT":
            self.state = "PLAY"
            return
        if self.state == "HORROR":
            return
        if self.state == "PAUSE":
            self.pause_click(e)
            return
        if getattr(self, "notice_approach_t", -1.0) >= 0.0:
            return
        if e.button == 2:
            self.panning = True
        elif e.button == 1:
            if self.cheat_hit(e.pos):
                for r, key in self.cheat_rects:
                    if r.collidepoint(e.pos):
                        self.cheat_action(key)
                        self.audio.play(self.audio.s_ui, 0.6)
                        return
                return
            if self.debug_hit(e.pos):
                for r, key in self.debug_rects:
                    if r.collidepoint(e.pos):
                        self.debug_action(key)
                        self.audio.play(self.audio.s_ui, 0.6)
                        return
                return
            if self.codex_open:
                for r, i in self.codex_rects:
                    if r.collidepoint(e.pos):
                        self.codex_tab = i
                        self.codex_scroll = 0
                        return
                return
            if self.finder_open:
                return
            for m in list(self.monitors):
                r = m.get("rect")
                if r and r.collidepoint(e.pos):
                    cr = m.get("close_rect")
                    if cr and cr.collidepoint(e.pos):
                        self.close_monitor(m["oid"])
                    else:
                        o = self.world.by_id.get(m["oid"])
                        if o:
                            self.recenter_on(o.oid)
                    return
            if self.dial_hit(e.pos):
                self.dial_drag = True
                self.dial_from_mouse(e.pos)
                return
            for r, mode in getattr(self, "mode_rects", []):
                if r.collidepoint(e.pos):
                    self.mode = mode
                    self.audio.play(self.audio.s_mode, 0.7)
                    return
            for r, t in getattr(self, "tool_rects", []):
                if r.collidepoint(e.pos):
                    self.tool = None if self.tool == t else t
                    self.audio.play(self.audio.s_mode, 0.7)
                    return
            for r, i in getattr(self, "tab_rects", []):
                if r.collidepoint(e.pos):
                    self.tab = i
                    if self.interference and i == 2 and self.calib is None:
                        self.start_calibration()
                    return
            for r, i in getattr(self, "help_nav_rects", []):
                if r.collidepoint(e.pos):
                    self.help_page = i
                    self.audio.play(self.audio.s_ui, 0.5)
                    return
            if getattr(self, "filter_rect", None) and self.filter_rect.collidepoint(e.pos):
                self.filter_i = (self.filter_i + 1) % len(FILTERS)
                return
            for r, oid in getattr(self, "log_rects", []):
                if r.collidepoint(e.pos):
                    self.recenter_on(oid)
                    return
            if self.tab == 2 and self.calib:
                self.calib_click(e.pos)

    def recenter_on(self, oid):
        o = self.world.by_id.get(oid)
        if not o:
            return
        self.cam_ra, self.cam_dec = o.ra, o.dec
        self.dial_p = self.z_to_p(max(0.0, o.z))
        self.z_dial = self.p_to_z(self.dial_p)
        self.zoom = max(self.zoom, 16.0)
        self.audio.play(self.audio.s_ui, 0.6)
        self.toast = "RECENTRED: %s" % o.name
        self.toast_t = 2.0

    def zoom_at(self, pos, factor):
        before = self.screen_to_world(*pos)
        self.zoom = clamp(self.zoom * factor, 1.1, 420.0)
        after = self.screen_to_world(*pos)
        self.cam_ra = (self.cam_ra + (before[0] - after[0] + 540) % 360 - 180) % 360
        self.cam_dec = clamp(self.cam_dec + (before[1] - after[1]), -89, 89)

    def dial_hit(self, pos):
        c = getattr(self, "dial_center", None)
        if not c:
            return False
        return math.hypot(pos[0] - c[0], pos[1] - c[1]) <= self.dial_R * 1.4

    def dial_from_mouse(self, pos):
        cx, cy = self.dial_center
        ang = math.degrees(math.atan2(pos[0] - cx, -(pos[1] - cy)))
        ang = clamp(ang, -DIAL_SWEEP_DEG, DIAL_SWEEP_DEG)
        p = (ang + DIAL_SWEEP_DEG) / (2 * DIAL_SWEEP_DEG)
        if abs(p - self.dial_p) > 0.0004:
            self.audio.play(self.audio.s_dial, 0.35)
        self.dial_p = p
        self.z_dial = self.p_to_z(p)

    # ---- debug panel ------------------------------------------------------
    def debug_hit(self, pos):
        if not (self.debug_unlocked and self.debug_open):
            return False
        for r, _ in self.debug_rects:
            if r.collidepoint(pos):
                return True
        return False

    def debug_action(self, key):
        w = self.world
        if w is None:
            return
        if key == "interf_on":
            if not self.interference:
                self.start_interference()
        elif key == "interf_off":
            if self.interference:
                self.end_interference()
        elif key == "log_spray":
            self.noticing_stage = 2
            self.post_noticing_interf = 0
            if self.interference:
                self.end_interference()
            self.start_interference()
        elif key == "calib_fight":
            self.noticing_stage = 2
            self.post_noticing_interf = 1
            if self.interference:
                self.end_interference()
            self.start_interference()
        elif key == "glitch":
            self.glitch_flash = 0.18
            self.shift = random.uniform(-9, 9)
            self.audio.play(self.audio.s_glitch, 0.7)
        elif key == "voice":
            self.audio.voice(pan=0.5)
        elif key == "dupe":
            self.dupe_cd = 0.0
        elif key == "reticle":
            self.noticing_stage = 2
            mouse = pygame.mouse.get_pos()
            for _ in range(30):
                x = random.uniform(self.L.sky.left + 40, self.L.sky.right - 40)
                y = random.uniform(self.L.sky.top + 40, self.L.sky.bottom - 40)
                if math.hypot(x - mouse[0], y - mouse[1]) > 220 * self.L.scale:
                    self.second_reticle = {"x": x, "y": y, "life": 8.0}
                    break
            self.toast = "SECOND RETICLE FORCED"
            self.toast_t = 2.0
        elif key == "spawn_anom":
            ra, dec = self.screen_to_world(*pygame.mouse.get_pos())
            o = w.spawn_anomaly(ra, dec, self.z_dial, self.game_hours, note="debug")
            self.log_add("DEBUG: spawned %s at cursor" % o.kind, CYAN, CAT_SYS, o.oid)
        elif key == "spawn_chain":
            ra, dec = self.screen_to_world(*pygame.mouse.get_pos())
            o = w.spawn_anomaly(ra, dec, self.z_dial, self.game_hours,
                                note="chain", chain=True)
            self.chain_markers.append({"oid": o.oid, "name": o.kind,
                                       "parent": "debug", "born": self.game_hours})
            self.log_add("DEBUG: chain anomaly spawned at cursor", CYAN, CAT_SYS, o.oid)
        elif key == "spawn_td":
            t = EVENT_TYPES[self.debug_td_idx % len(EVENT_TYPES)]
            self.spawn_time_domain_event(t)
            self.toast = "T-D: %s" % t["kind"]
            self.toast_t = 2.0
        elif key == "next_td":
            self.debug_td_idx = (self.debug_td_idx + 1) % len(EVENT_TYPES)
            t = EVENT_TYPES[self.debug_td_idx]
            self.toast = "T-D TYPE: %s  (window %.1fh)" % (t["kind"], t["dur"])
            self.toast_t = 3.0
        elif key == "force_dim":
            cands = [o for o in w.objects if o.variable]
            if cands:
                s = random.choice(cands)
                s.dim_phase = -self.game_hours % s.dim_period
                self.log_add("DEBUG: forced dim on %s" % s.name, CYAN, CAT_SYS, s.oid)
        elif key == "noticing":
            self.noticing_stage = 1
            cands = [o for o in w.objects if o.kind == "anomaly" and not o.spawn]
            if cands:
                self.noticing_oid = random.choice(cands).oid
            self.toast = "NOTICING ARMED"
            self.toast_t = 3.0
            if self.last_slot is not None:
                self.save_game(self.last_slot)
        elif key == "fire_noticing":
            self.noticing_stage = 1
            if self.noticing_oid is None:
                cands = [o for o in w.objects
                         if o.kind == "anomaly" and not o.spawn]
                if cands:
                    self.noticing_oid = random.choice(cands).oid
            if self.noticing_oid is not None:
                self.begin_notice_approach()
        elif key == "horror":
            self.horror_t = 0.0
            self.state = "HORROR"
        elif key == "clear_noticing":
            self.noticing_stage = 0
            self.noticing_oid = None
            self.horror_t = -1.0
            self.notice_reveal_t = -1.0
            self.notice_approach_t = -1.0
            self.notice_approach_start = None
            self.notice_target_oid = None
            if self.state == "HORROR":
                self.state = "PLAY"
            self.toast = "NOTICING CLEARED"
            self.toast_t = 2.0
        elif key == "reveal":
            self.debug_reveal = not self.debug_reveal
            self.toast = "REVEAL %s" % ("ON" if self.debug_reveal else "OFF")
            self.toast_t = 2.0
        elif key == "scan_nearby":
            ra, dec = self.screen_to_world(*pygame.mouse.get_pos())
            n = 0
            for o in list(w.objects):
                if self.ang_sep(ra, dec, o.ra, o.dec) <= 20 and not self.obj_done(o):
                    self.complete_scan(o)
                    n += 1
            self.log_add("DEBUG: catalogued %d contacts within 20 deg" % n, CYAN, CAT_SYS)
        elif key == "resolve_all":
            n = 0
            for o in w.objects:
                if o.kind == "anomaly" and o.stage < 2:
                    if o.stage == 0:
                        o.stage = 1
                        self.stats["anom"] += 1
                    o.stage = 2
                    o.stage_time = self.game_hours
                    self.stats["resolved"] += 1
                    n += 1
            self.log_add("DEBUG: resolved %d anomalies" % n, CYAN, CAT_SYS)
            self.check_milestones()
        elif key == "score":
            self.score += 1000
            self.check_milestones()
        elif key == "advance":
            self.game_hours += 6.0
            self.log_add("DEBUG: advanced 6 game hours", CYAN, CAT_SYS)
        elif key == "unlock_codex":
            for name in CODEX_CELESTIAL:
                self.codex_seen.add("cat:" + name)
            for name in CODEX_ANOMALY:
                self.codex_seen.add("anom:" + name)
            self.toast = "CODEX UNLOCKED"
            self.toast_t = 2.0

    def render_debug(self):
        L = self.L
        f = self.fonts["xs"]
        rowh = int(17 * L.scale)
        w = int(clamp(L.w * 0.30, 250, 360))
        h = int(20 * L.scale) + rowh * len(DEBUG_ACTIONS) + int(18 * L.scale)
        x = 12
        y = L.top_h + int(10 * L.scale)
        if self.monitors:
            mh = int(94 * L.scale)
            y += len(self.monitors) * (mh + int(8 * L.scale))
        if y + h > L.sky.bottom:
            y = max(L.top_h + 8, L.sky.bottom - h)
        rect = pygame.Rect(x, y, w, h)
        panel_rect(self.screen, rect, border=CYAN, fill=(0, 20, 26, 220))
        text_at(self.screen, f, "DEBUG  --  ` to close",
                (rect.x + 6, rect.y + 4), CYAN, glow=True)
        self.debug_rects = []
        yy = rect.y + int(21 * L.scale)
        mouse = pygame.mouse.get_pos()
        for label, key in DEBUG_ACTIONS:
            r = pygame.Rect(rect.x + 4, yy, rect.w - 8, rowh - 2)
            hover = r.collidepoint(mouse)
            on = (key == "reveal" and self.debug_reveal)
            col = AMBER if on else (PHOS if hover else PHOS_DIM)
            if hover:
                pygame.draw.rect(self.screen, (0, 40, 34), r)
            text_at(self.screen, f, label, (r.x + 4, r.y + 1), col, glow=hover)
            self.debug_rects.append((r, key))
            yy += rowh
        text_at(self.screen, f,
                "z=%.3f mode=%s tool=%s interf=%s" %
                (self.z_dial, self.mode, self.tool or "-",
                 "Y" if self.interference else "n"),
                (rect.x + 6, yy + 2), PHOS_FAINT, glow=False)

    # ---- cheat panel ------------------------------------------------------
    def cheat_hit(self, pos):
        if not (self.cheat_unlocked and self.cheat_open):
            return False
        for r, _ in self.cheat_rects:
            if r.collidepoint(pos):
                return True
        return False

    def cheat_action(self, key):
        w = self.world
        if w is None:
            return
        if key == "c_reveal":
            self.debug_reveal = not self.debug_reveal
        elif key == "c_no_sol":
            self.cheat_no_solar = not self.cheat_no_solar
        elif key == "c_wide_scan":
            self.cheat_wide_scan = not self.cheat_wide_scan
        elif key == "c_fast":
            self.cheat_fast_scan = not self.cheat_fast_scan
        elif key == "c_inf_hold":
            self.cheat_inf_hold = not self.cheat_inf_hold
        elif key == "c_z0":
            self.dial_p = 0.0
            self.z_dial = 0.0
        elif key == "c_z01":
            self.dial_p = self.z_to_p(0.1)
            self.z_dial = 0.1
        elif key == "c_z1":
            self.dial_p = self.z_to_p(1.0)
            self.z_dial = 1.0
        elif key == "c_adv24":
            self.game_hours += 24.0
        elif key == "c_adv7d":
            self.game_hours += 24.0 * 7.0
        elif key == "c_resolve_all":
            n = 0
            for o in w.objects:
                if o.kind == "anomaly" and o.stage < 2:
                    if o.stage == 0:
                        o.stage = 1
                        self.stats["anom"] += 1
                    o.stage = 2
                    o.stage_time = self.game_hours
                    self.stats["resolved"] += 1
                    n += 1
            self.log_add("CHEAT: resolved %d anomalies" % n, CYAN, CAT_SYS)
        elif key == "c_reset_stages":
            for o in w.objects:
                o.stage = 0
            self.stats["stars"] = 0
            self.stats["deep"] = 0
            self.stats["anom"] = 0
            self.stats["resolved"] = 0
            self.log_add("CHEAT: all stages reset", CYAN, CAT_SYS)
        elif key == "c_spawn_anom":
            ra, dec = self.screen_to_world(*pygame.mouse.get_pos())
            w.spawn_anomaly(ra, dec, self.z_dial, self.game_hours, note="cheat")
        elif key == "c_spawn_chain":
            ra, dec = self.screen_to_world(*pygame.mouse.get_pos())
            o = w.spawn_anomaly(ra, dec, self.z_dial, self.game_hours,
                                note="chain", chain=True)
            self.chain_markers.append({"oid": o.oid, "name": o.kind,
                                       "parent": "cheat", "born": self.game_hours})
        elif key == "c_kill_transients":
            for o in list(self.transients):
                if o in w.objects:
                    w.objects.remove(o)
                w.by_id.pop(o.oid, None)
            self.transients = []
            w.reindex()
        elif key == "c_score":
            self.score += 5000
            self.check_milestones()

    def render_cheat(self):
        L = self.L
        f = self.fonts["xs"]
        rowh = int(17 * L.scale)
        w = int(clamp(L.w * 0.30, 250, 360))
        h = int(20 * L.scale) + rowh * len(CHEAT_ACTIONS) + int(18 * L.scale)
        x = L.w - w - 12
        y = L.top_h + int(10 * L.scale)
        if y + h > L.sky.bottom:
            y = max(L.top_h + 8, L.sky.bottom - h)
        rect = pygame.Rect(x, y, w, h)
        panel_rect(self.screen, rect, border=RED_WARN, fill=(20, 6, 6, 220))
        text_at(self.screen, f, "CHEAT  --  ` to close",
                (rect.x + 6, rect.y + 4), RED_WARN, glow=True)
        self.cheat_rects = []
        yy = rect.y + int(21 * L.scale)
        mouse = pygame.mouse.get_pos()
        flag_map = {
            "c_reveal": self.debug_reveal,
            "c_no_sol": self.cheat_no_solar,
            "c_wide_scan": self.cheat_wide_scan,
            "c_fast": self.cheat_fast_scan,
            "c_inf_hold": self.cheat_inf_hold,
        }
        for label, key in CHEAT_ACTIONS:
            r = pygame.Rect(rect.x + 4, yy, rect.w - 8, rowh - 2)
            hover = r.collidepoint(mouse)
            on = flag_map.get(key, False)
            col = AMBER if on else (PHOS if hover else PHOS_DIM)
            if hover:
                pygame.draw.rect(self.screen, (40, 0, 0), r)
            text_at(self.screen, f, label, (r.x + 4, r.y + 1), col, glow=hover)
            self.cheat_rects.append((r, key))
            yy += rowh
        text_at(self.screen, f,
                "seed=%d score=%d" % (self.seed, self.score),
                (rect.x + 6, yy + 2), PHOS_FAINT, glow=False)

    # ---- horror / noticing -----------------------------------------------
    def noticer_says(self, text, oid=None):
        """Every log line the noticer writes plays the same pitched chime.
        This is its voice. Nothing else uses s_horror."""
        self.log.append(LogEntry("", text, RED_WARN, CAT_SYS, oid))
        self.audio.play(self.audio.s_horror, 1.0)

    def begin_notice_approach(self):
        """The drag-in. Relocates the contact to a genuine spot on the
        map, then hauls the camera -- and the player's own cursor -- to
        it over NOTICE_APPROACH_DURATION seconds, like a forced camera
        pan in a cutscene. Nothing gets written to the log and nothing
        else in update() runs until the array has actually arrived, so
        there's no way to look away before it lands. Once the approach
        finishes it hands off to fire_noticing_event()."""
        o = self.world.by_id.get(self.noticing_oid)
        if o is None:
            self.fire_noticing_event()
            return

        # relocate it now, before the drag starts, so the camera has a
        # real destination and this is an actual anomaly sitting on the
        # map, not something that appears out of nowhere.
        o.ra = (o.ra + random.uniform(-6.0, 6.0)) % 360.0
        o.dec = clamp(o.dec + random.uniform(-5.0, 5.0), -88, 88)
        self.world.reindex()

        try:
            mx, my = pygame.mouse.get_pos()
        except Exception:
            mx, my = self.L.w * 0.5, self.L.sky.centery
        self.notice_target_oid = o.oid
        self.notice_approach_start = (self.cam_ra, self.cam_dec, self.zoom, mx, my)
        self.notice_approach_t = 0.0
        self.panning = False
        self.dial_drag = False
        self.radial_open = False
        self.L.panel_open = True
        self.tab = 0
        self.audio.play(self.audio.s_anom, 1.0)

    def update_notice_approach(self, dt):
        o = self.world.by_id.get(self.notice_target_oid)
        if o is None or self.notice_approach_start is None:
            self.notice_approach_t = -1.0
            self.fire_noticing_event()
            return

        self.notice_approach_t += dt
        t = clamp(self.notice_approach_t / NOTICE_APPROACH_DURATION, 0.0, 1.0)
        ease = t * t * (3.0 - 2.0 * t)  # smoothstep -- eases in, settles hard

        from_ra, from_dec, from_zoom, from_mx, from_my = self.notice_approach_start
        target_zoom = max(from_zoom, NOTICE_APPROACH_ZOOM)

        dra = (o.ra - from_ra + 540.0) % 360.0 - 180.0
        self.cam_ra = (from_ra + dra * ease) % 360.0
        self.cam_dec = from_dec + (o.dec - from_dec) * ease
        self.zoom = from_zoom + (target_zoom - from_zoom) * ease

        tx, ty = self.world_to_screen(o.ra, o.dec)
        mx = from_mx + (tx - from_mx) * ease
        my = from_my + (ty - from_my) * ease
        try:
            pygame.mouse.set_pos(
                int(clamp(mx, 2, self.L.w - 2)),
                int(clamp(my, self.L.sky.top + 2, self.L.sky.bottom - 2)))
        except Exception:
            pass

        if t >= 1.0:
            self.notice_approach_t = -1.0
            self.notice_approach_start = None
            self.fire_noticing_event()

    def fire_noticing_event(self):
        stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
        try:
            host = socket.gethostname() or "operator"
        except Exception:
            host = "operator"
        self.noticer_says(NOTICE_MSG.format(host=host), self.noticing_oid)

        self.noticing_stage = 2
        if self.last_slot is not None:
            try:
                self.save_game(self.last_slot)
            except Exception:
                pass

        # --- the reveal beat --------------------------------------------
        # Stay in PLAY a little longer so the player actually sees and
        # hears the noticer's line land -- the log panel is forced open
        # on the log tab -- before the static takeover begins. The
        # transition into HORROR itself happens in update(), once
        # notice_reveal_t runs out.
        self.L.panel_open = True
        self.tab = 0
        self.notice_reveal_t = 0.0

    def update_horror(self, dt):
        try:
            self.horror_t += dt
            f = clamp(self.horror_t / HORROR_DURATION, 0.0, 1.0)
            self.audio.set_static(0.08 + 0.92 * f, 0.5)
            self.audio.set_hum_pan(0.5, 1.0 + 2.0 * f)
            if self.horror_t >= HORROR_DURATION:
                if self.last_slot is not None:
                    try:
                        self.save_game(self.last_slot)
                    except Exception:
                        pass
                self.restart_game()
        except Exception:
            try:
                if self.last_slot is not None and self.world is not None:
                    self.save_game(self.last_slot)
            except Exception:
                pass
            raise

    def restart_game(self):
        self.audio.stop_all()
        try:
            pygame.quit()
        except Exception:
            pass
        try:
            if getattr(sys, "frozen", False):
                subprocess.Popen([sys.executable])
            else:
                subprocess.Popen([sys.executable] + sys.argv)
        except Exception:
            pass
        sys.exit(0)

    # ================================================================ UPDATE
    def update(self, dt):
        if self.notice_approach_t >= 0.0:
            self.update_notice_approach(dt)
            return

        if self.notice_reveal_t >= 0.0:
            self.notice_reveal_t += dt
            if self.notice_reveal_t >= NOTICE_REVEAL_DURATION:
                self.notice_reveal_t = -1.0
                self.state = "HORROR"
                self.horror_t = 0.0
                return

        if self.pending_debug_t > 0.0:
            now = time.time()
            if now - self.pending_debug_t > DEBUG_FIRE_DELAY:
                if len(self.debug_keybuf) >= len(DEBUG_SEQ):
                    last6 = [x[0] for x in self.debug_keybuf[-len(DEBUG_SEQ):]]
                    last_key, last_time = self.debug_keybuf[-1]
                    if last6 == DEBUG_SEQ and last_key == pygame.K_z \
                            and now - last_time > DEBUG_FIRE_DELAY:
                        self.pending_debug_t = 0.0
                        self.debug_keybuf = []
                        self.debug_rects = []
                        if not self.debug_unlocked:
                            self.debug_unlocked = True
                            self.debug_open = True
                            self.audio.play(self.audio.s_resolve, 1.0)
                            self.log_add("DEBUG MODE UNLOCKED -- ` toggles the panel",
                                         CYAN, CAT_SYS)
                            self.toast = "DEBUG MODE UNLOCKED"
                            self.toast_t = 3.0
                        else:
                            self.debug_open = not self.debug_open
                else:
                    self.pending_debug_t = 0.0

        keys = pygame.key.get_pressed()
        prev_radial = self.radial_open
        self.radial_open = keys[pygame.K_x] and not self.finder_open
        if self.radial_open and not prev_radial:
            self.radial_sel = 0
        if self.radial_open:
            mx, my = pygame.mouse.get_pos()
            cx, cy = self.L.w * 0.5, self.L.sky.centery
            dx, dy = mx - cx, my - cy
            if math.hypot(dx, dy) > 20 * self.L.scale:
                ang = math.atan2(dy, dx)
                slots = len(TOOLS) + 1
                seg = (math.pi * 2) / slots
                idx = int(((ang + math.pi / 2) % (math.pi * 2)) / seg)
                self.radial_sel = idx % slots
        elif prev_radial and not self.radial_open:
            if self.radial_sel == len(TOOLS):
                self.tool = None
            else:
                t = TOOLS[self.radial_sel]
                self.tool = None if self.tool == t else t
            self.audio.play(self.audio.s_mode, 0.6)
            self.toast = "TOOL: %s" % (self.tool or "none")
            self.toast_t = 1.4

        self.session_t += dt
        self.game_hours += dt / REAL_SECONDS_PER_GAME_HOUR
        self.fx_i += dt * 14
        self.toast_t = max(0, self.toast_t - dt)
        self.miss_cd = max(0, self.miss_cd - dt)
        self.glitch_flash = max(0, self.glitch_flash - dt)
        self.shift *= 0.82
        self.spectrum_phase += dt * 6.0
        self.hint_t += dt
        if self.hint_t > 26:
            self.hint_t = 0
            self.hint_i = (self.hint_i + 1) % len(HINTS)

        fast = keys[pygame.K_LSHIFT] or keys[pygame.K_RSHIFT]

        pan = (52.0 / self.zoom) * (3.4 if fast else 1.0) * 60 * dt
        dx = (keys[pygame.K_d] or keys[pygame.K_RIGHT]) - (keys[pygame.K_a] or keys[pygame.K_LEFT])
        dy = (keys[pygame.K_w] or keys[pygame.K_UP]) - (keys[pygame.K_s] or keys[pygame.K_DOWN])
        if self.tab == 2 and self.calib:
            dx = dy = 0
        if dx:
            k = max(0.15, math.cos(math.radians(self.cam_dec)))
            self.cam_ra = (self.cam_ra + dx * pan / k) % 360
        if dy:
            self.cam_dec = clamp(self.cam_dec + dy * pan, -89, 89)
        if keys[pygame.K_EQUALS] or keys[pygame.K_PLUS]:
            self.zoom = clamp(self.zoom * (1 + dt), 1.1, 420)
        if keys[pygame.K_MINUS]:
            self.zoom = clamp(self.zoom * (1 - dt), 1.1, 420)

        step = (0.22 if fast else 0.045) * dt
        d = (keys[pygame.K_e] - keys[pygame.K_q])
        if d and not (self.tab == 2 and self.calib):
            prev = self.dial_p
            self.dial_p = clamp(self.dial_p + d * step, 0, 1)
            self.z_dial = self.p_to_z(self.dial_p)
            if int(prev * 260) != int(self.dial_p * 260):
                self.audio.play(self.audio.s_dial, 0.30)

        self.update_events(dt)

        mouse = pygame.mouse.get_pos()
        pan_l = clamp(mouse[0] / max(1, self.L.w), 0, 1)
        ra_m, dec_m = self.screen_to_world(*mouse)
        sol = self.solar_noise(ra_m, dec_m)
        self.sol_noise = sol
        self.audio.set_hum_pan(pan_l, 0.85 + 0.3 * math.sin(self.session_t * 0.3))
        base_static = 0.03 + sol * 0.30
        if self.interference:
            base_static = 0.55 + 0.1 * math.sin(self.session_t * 9)
        self.audio.set_static(base_static, pan_l)

        if self.tab == 2 and self.calib:
            self.update_calibration(dt, keys)

        pressed = pygame.mouse.get_pressed()
        scanning_allowed = (not self.interference) and self.L.sky.collidepoint(mouse) and \
                           not (self.L.panel_open and self.L.panel.collidepoint(mouse)) and \
                           not self.monitor_hit(mouse) and \
                           not self.debug_hit(mouse) and \
                           not self.cheat_hit(mouse) and \
                           not self.finder_open and not self.radial_open and \
                           not self.codex_open
        if self.monitor_mode:
            self.scan_p = max(0.0, self.scan_p - dt * 2.2)
            self.target = None
            self.update_monitor_scan(dt, mouse, pressed[0] and scanning_allowed)
        else:
            self.mon_scan_p = max(0.0, self.mon_scan_p - dt * 3.0)
            self.mon_target = None
            self.update_scanning(dt, mouse, pressed[0] and scanning_allowed)
        self.update_monitors(dt)
        self.update_dimming(dt)

        self.dim_markers = [m for m in self.dim_markers if m["oid"] in self.world.by_id]
        self.chain_markers = [m for m in self.chain_markers
                              if m["oid"] in self.world.by_id
                              and self.world.by_id[m["oid"]].stage < 2]

        self.update_second_reticle(dt)

    # ---- dimming ----------------------------------------------------------
    # ---- second reticle ---------------------------------------------------
    def update_second_reticle(self, dt):
        if self.noticing_stage != 2:
            self.second_reticle = None
            return
        if self.second_reticle is None:
            self.second_reticle_cd -= dt
            if self.second_reticle_cd <= 0:
                self.second_reticle_cd = random.uniform(90.0, 220.0)
                mouse = pygame.mouse.get_pos()
                for _ in range(20):
                    x = random.uniform(self.L.sky.left + 40, self.L.sky.right - 40)
                    y = random.uniform(self.L.sky.top + 40, self.L.sky.bottom - 40)
                    if math.hypot(x - mouse[0], y - mouse[1]) > 220 * self.L.scale:
                        self.second_reticle = {
                            "x": x, "y": y,
                            "life": random.uniform(4.0, 8.0),
                        }
                        break
        else:
            r = self.second_reticle
            r["life"] -= dt
            mouse = pygame.mouse.get_pos()
            dx = mouse[0] - r["x"]
            dy = mouse[1] - r["y"]
            d = math.hypot(dx, dy)
            speed = clamp((d - 60 * self.L.scale) / (240.0 * self.L.scale), 0, 1)
            if d > 1e-3:
                r["x"] += (dx / d) * speed * 90.0 * dt * self.L.scale
                r["y"] += (dy / d) * speed * 90.0 * dt * self.L.scale
            if r["life"] <= 0:
                self.second_reticle = None

    def render_second_reticle(self):
        if self.noticing_stage != 2 or self.second_reticle is None:
            return
        r = self.second_reticle
        fade = clamp(r["life"] / 1.5, 0.0, 1.0)
        col = dim_color((140, 30, 40), 0.6 + 0.4 * fade)
        pygame.draw.circle(self.screen, col, (int(r["x"]), int(r["y"])), 2)
        if fade > 0.5:
            pygame.draw.circle(self.screen, (60, 14, 20),
                               (int(r["x"]), int(r["y"])), 4, 1)

    def update_dimming(self, dt):
        have = {m["oid"] for m in self.dim_markers}
        for o in self.world.objects:
            if not o.variable:
                continue
            dim = o.is_dimmed(self.game_hours)
            if dim and o.oid not in have:
                self.dim_markers.append({"oid": o.oid, "name": o.name,
                                         "started": self.game_hours})
                self.log_add(
                    "LUMINOSITY DROP: %s -- dip in progress. Marker set." % o.name,
                    AMBER, CAT_ANOM, o.oid)
                self.audio.play(self.audio.s_anom, 0.6)
            elif not dim and o.oid in have:
                self.dim_markers = [m for m in self.dim_markers if m["oid"] != o.oid]

    # ---- ambient events ---------------------------------------------------
    def update_events(self, dt):
        self.glitch_cd -= dt
        if self.glitch_cd <= 0:
            self.glitch_cd = random.uniform(22, 55)
            self.glitch_flash = random.uniform(0.05, 0.16)
            self.shift = random.uniform(-7, 7)
            self.audio.play(self.audio.s_glitch, 0.5)
            if random.random() < 0.65:
                self.log_add(random.choice(GLITCH_LINES), PHOS_DIM, CAT_SYS)

        self.dupe_cd -= dt
        if self.dupe_cd <= 0 and self.dupe is None:
            self.dupe_cd = random.uniform(150, 330)
            cand = [o for o in self.world.nearby(self.cam_ra, self.cam_dec, 2)
                    if o.kind == "star" and o.mag < 6.5]
            if cand:
                o = random.choice(cand)
                self.dupe = [o, random.uniform(2.5, 5.0),
                             (random.uniform(-14, 14), random.uniform(-14, 14))]
        if self.dupe:
            self.dupe[1] -= dt
            if self.dupe[1] <= 0:
                self.dupe = None

        self.voice_cd -= dt
        if self.voice_cd <= 0:
            self.voice_cd = random.uniform(210, 520)
            self.audio.voice(pan=random.uniform(0.15, 0.85))

        self.transient_cd -= dt
        if self.transient_cd <= 0:
            self.transient_cd = random.uniform(90, 200)
            self.spawn_time_domain_event()

        # advance active time-domain events
        if self.active_events:
            still = []
            for e in self.active_events:
                o = self.world.by_id.get(e["oid"]) if e["oid"] is not None else None
                age = self.game_hours - e["born"]

                if o is not None and o.stage >= 2:
                    self.log_add("%s RESOLVED [%s]: %s"
                                 % (e["kind"].upper(), e["kind"], e["resolve"]),
                                 AMBER, CAT_ANOM, o.oid)
                    self.audio.play(self.audio.s_resolve, 0.8)
                    if o in self.world.objects:
                        self.world.objects.remove(o)
                    self.world.by_id.pop(o.oid, None)
                    self.world.reindex()
                    continue

                if age > e["dur"]:
                    if o is not None:
                        if o in self.world.objects:
                            self.world.objects.remove(o)
                        self.world.by_id.pop(o.oid, None)
                        self.world.reindex()
                    continue

                still.append(e)
            self.active_events = still

        if not self.interference:
            self.next_interf -= dt
            if self.next_interf <= 0 and self.session_t > 90:
                self.start_interference()
        else:
            self.interf_t += dt

    def start_interference(self):
        self.interference = True
        self.interf_t = 0.0
        self.scan_p = 0.0
        self.calib = None
        self.audio.play(self.audio.s_glitch, 1.0)
        self.log_add("!! CARRIER LOST -- BROADBAND INTERFERENCE ACROSS ALL BANDS",
                     RED_WARN, CAT_SYS)
        self.log_add("Open CALIB tab (TAB) and re-phase the three receiver channels.",
                     AMBER, CAT_SYS)

        if self.noticing_stage == 2:
            self.post_noticing_interf += 1

            if self.post_noticing_interf == 1:
                for _ in range(random.randint(35, 55)):
                    n = random.randint(24, 72)
                    chars = "".join(
                        random.choice("!@#$%^&*()_+-=[]{}|;:,.<>?/\\~`0123456789"
                                      "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
                        for _ in range(n))
                    self.log.append(LogEntry("", chars, RED_WARN, CAT_SYS))
                self.audio.play(self.audio.s_horror, 1.0)
                self.toast = "SIGNAL LOST -- THE LOG IS BEING WRITTEN TO"
                self.toast_t = 6.0
                return

            if self.post_noticing_interf == 2:
                self.toast = "SIGNAL LOST -- THE SERVO IS FIGHTING YOU"
                self.toast_t = 6.0
                return

        self.toast = "SIGNAL LOST -- PRESS TAB, OPEN CALIB"
        self.toast_t = 6.0

    def end_interference(self):
        was_fight = (self.calib is not None and self.calib.get("fight"))
        self.interference = False
        self.calib = None
        self.next_interf = random.uniform(300, 560)
        self.score += 75
        self.stats["fixes"] += 1
        self.audio.play(self.audio.s_resolve, 0.9)
        self.log_add("CHANNELS RE-PHASED. Carrier recovered. +75", PHOS, CAT_SYS)

        if was_fight:
            self.noticer_says("SOMETHING DISENGAGED.")

        self.toast = "CARRIER RECOVERED"
        self.toast_t = 3.0
        self.check_milestones()

    def spawn_time_domain_event(self, t=None):
        """Fire one event from the taxonomy. GRB and FRB are log-only."""
        if t is None:
            t = random.choice(EVENT_TYPES)
        ra = (self.cam_ra + random.uniform(-14, 14)) % 360
        dec = clamp(self.cam_dec + random.uniform(-10, 10), -88, 88)

        hosts = [o for o in self.world.objects
                 if not o.proc and o.stage >= 2
                 and o.kind in ("galaxy", "star", "remnant", "exotic")]
        host = random.choice(hosts) if (hosts and random.random() < 0.6) else None
        if host is not None:
            ra, dec = host.ra, host.dec

        who = host.name if host is not None else "unresolved field"
        self.log_add(t["log"] % who,
                     RED_WARN if t["dur"] == 0.0 else AMBER, CAT_ANOM)

        if t["dur"] == 0.0:
            self.audio.play(self.audio.s_glitch, 0.5)
            return

        o = self.world.spawn_anomaly(
            ra, dec, host.z if host is not None else 0.0,
            self.game_hours, note=t["kind"])
        o.name = t["kind"]
        o.blurb = t["log"] % who
        o.band = t["band"]
        self.active_events.append({
            "oid": o.oid, "kind": t["kind"], "dur": t["dur"],
            "born": self.game_hours, "band": t["band"],
            "resolve": t["resolve"], "log": t["log"] % who,
        })
        self.log_add("TIME-DOMAIN EVENT: %s. Window %.1fh."
                     % (t["kind"], t["dur"]), AMBER, CAT_ANOM, o.oid)

    # ---- calibration minigame --------------------------------------------
    def start_calibration(self):
        fight = (self.noticing_stage == 2 and self.post_noticing_interf == 2)
        self.calib = {
            "bands": [{"cur": random.uniform(0.05, 0.95),
                       "tgt": random.uniform(0.15, 0.85),
                       "lock": False,
                       "freq": 1.6 + i * 1.1} for i in range(3)],
            "sel": 0,
            "t": 0.0,
            "fight": fight,
            "fight_dir": random.choice([-1, 1]) if fight else 0,
        }
        self.audio.play(self.audio.s_ui, 0.7)

    def calib_key(self, k):
        c = self.calib
        if k in (pygame.K_UP, pygame.K_w):
            c["sel"] = (c["sel"] - 1) % 3
        elif k in (pygame.K_DOWN, pygame.K_s):
            c["sel"] = (c["sel"] + 1) % 3
        elif k in (pygame.K_SPACE, pygame.K_RETURN):
            b = c["bands"][c["sel"]]
            if b["lock"]:
                return
            if abs(b["cur"] - b["tgt"]) < 0.035:
                b["lock"] = True
                b["cur"] = b["tgt"]
                self.audio.play(self.audio.s_lock, 0.8)
                if all(x["lock"] for x in c["bands"]):
                    self.end_interference()
            else:
                self.audio.play(self.audio.s_deny, 0.7)

    def calib_click(self, pos):
        for i, r in enumerate(getattr(self, "calib_rects", [])):
            if r.collidepoint(pos):
                self.calib["sel"] = i
                return

    def update_calibration(self, dt, keys):
        c = self.calib
        c["t"] += dt
        b = c["bands"][c["sel"]]

        if c.get("fight"):
            for band in c["bands"]:
                if not band["lock"]:
                    band["cur"] = clamp(
                        band["cur"] + c["fight_dir"] * 0.11 * dt, 0, 1)

        if not b["lock"]:
            spd = (0.55 if (keys[pygame.K_LSHIFT] or keys[pygame.K_RSHIFT]) else 0.16) * dt
            mv = (keys[pygame.K_RIGHT] or keys[pygame.K_d]) - \
                 (keys[pygame.K_LEFT] or keys[pygame.K_a])
            if mv:
                b["cur"] = clamp(b["cur"] + mv * spd, 0, 1)
                err = abs(b["cur"] - b["tgt"])
                if err < 0.09 and random.random() < 0.25:
                    self.audio.play(self.audio.s_tick, 0.35 * (1 - err / 0.09))

    # ---- target acquisition ----------------------------------------------
    def scan_requirement(self, obj):
        if obj.kind == "anomaly":
            base = 2.4 if obj.stage == 0 else 3.0
        elif obj.kind == "star":
            base = 0.95 if obj.proc else 1.35
            if obj.variable and obj.is_dimmed(self.game_hours) and obj.stage >= 2:
                base = 2.4
        elif obj.kind in ("quasar", "exotic"):
            base = 2.0
        else:
            base = 1.7
        if not self.mode_match(obj):
            base *= 3.2
        base *= 1.0 + 2.0 * self.solar_noise(obj.ra, obj.dec)
        if self.cheat_fast_scan:
            base *= 0.15
        return base

    def obj_done(self, obj):
        if obj.kind == "anomaly":
            return obj.stage >= 2
        if obj.kind == "star" and obj.variable:
            return obj.stage >= 3
        return obj.stage >= 2

    def find_target(self, mouse):
        ra, dec = self.screen_to_world(*mouse)
        radius = 24.0 * self.L.scale
        if self.cheat_wide_scan:
            radius *= 2.2
        elif self.tool == "INTERF":
            radius *= 1.5
        best, best_d = None, radius
        for o in self.world.nearby(ra, dec, 1):
            st = self.band_strength(o)
            if st < 0.2 and not self.debug_reveal:
                continue
            x, y = self.world_to_screen(o.ra, o.dec)
            d = math.hypot(x - mouse[0], y - mouse[1])
            if d < best_d:
                best_d, best = d, o
        return best

    def signal_strength(self, mouse):
        ra, dec = self.screen_to_world(*mouse)
        best = 0.0
        for o in self.world.nearby(ra, dec, 1):
            if self.obj_done(o):
                continue
            if self.band_strength(o) < 0.25:
                continue
            x, y = self.world_to_screen(o.ra, o.dec)
            d = math.hypot(x - mouse[0], y - mouse[1])
            v = clamp(1.0 - d / (170.0 * self.L.scale), 0, 1)
            if o.kind == "anomaly":
                v *= 1.15
            best = max(best, v)
        return clamp(best, 0, 1)

    def update_scanning(self, dt, mouse, down):
        hit = self.find_target(mouse)

        if hit is None:
            if self.target is not None and self.scan_p > 0.35 and self.miss_cd <= 0:
                if self.target.kind == "anomaly" and self.target.trait in ("shy", "flicker"):
                    self.audio.play(self.audio.s_miss, 0.9,
                                    pan=clamp(mouse[0] / self.L.w, 0, 1))
                    self.miss_cd = 4.0
            self.target = None
            self.hold_pos = None
            self.scan_p = max(0, self.scan_p - dt * 2.2)
            return

        self.target = hit

        if hit.kind == "anomaly" and hit.trait == "shy" and hit.stage < 2:
            x, y = self.world_to_screen(hit.ra, hit.dec)
            d = math.hypot(x - mouse[0], y - mouse[1])
            if d < 46 * self.L.scale:
                a = math.atan2(y - mouse[1], x - mouse[0])
                hit.ra = (hit.ra + math.cos(a) * 0.9 / self.zoom) % 360
                hit.dec = clamp(hit.dec - math.sin(a) * 0.9 / self.zoom, -89, 89)

        if not down or self.obj_done(hit):
            self.scan_p = max(0, self.scan_p - dt * 2.2)
            self.hold_pos = None
            return

        if hit.kind == "anomaly" and hit.stage == 1 and \
                self.game_hours - hit.stage_time < 3.0:
            self.scan_p = 0.0
            return

        if self.hold_pos is None:
            self.hold_pos = mouse
        drift_cap = 10**9 if self.cheat_inf_hold else 12 * self.L.scale
        if math.hypot(mouse[0] - self.hold_pos[0], mouse[1] - self.hold_pos[1]) > drift_cap:
            self.hold_pos = mouse
            self.scan_p = max(0, self.scan_p - dt * 3.0)
            return

        need = self.scan_requirement(hit)
        self.scan_need = need
        rate = dt * clamp(self.band_strength(hit), 0.18, 1.0)
        prev = self.scan_p
        self.scan_p = min(need, self.scan_p + rate)

        notch = int(self.scan_p * 5)
        if notch != self.tick_notch:
            self.tick_notch = notch
            self.audio.play(self.audio.s_tick, 0.5, pan=clamp(mouse[0] / self.L.w, 0, 1))

        if prev < need <= self.scan_p:
            self.complete_scan(hit)
            self.scan_p = 0.0
            self.tick_notch = -1

    # ---- monitor scanning -------------------------------------------------
    def monitor_hit(self, pos):
        for m in self.monitors:
            r = m.get("rect")
            if r and r.collidepoint(pos):
                return True
        return False

    def find_target_monitor(self, mouse):
        ra, dec = self.screen_to_world(*mouse)
        best, best_d = None, 26.0 * self.L.scale
        for o in self.world.nearby(ra, dec, 1):
            if self.band_strength(o) < 0.05:
                continue
            x, y = self.world_to_screen(o.ra, o.dec)
            d = math.hypot(x - mouse[0], y - mouse[1])
            if d < best_d:
                best_d, best = d, o
        return best

    def update_monitor_scan(self, dt, mouse, down):
        hit = self.find_target_monitor(mouse)
        self.mon_target = hit
        if hit is None or not down:
            self.mon_scan_p = max(0.0, self.mon_scan_p - dt * 3.0)
            self.mon_hold_pos = None
            return
        if self.mon_hold_pos is None:
            self.mon_hold_pos = mouse
        if math.hypot(mouse[0] - self.mon_hold_pos[0],
                      mouse[1] - self.mon_hold_pos[1]) > 14 * self.L.scale:
            self.mon_hold_pos = mouse
            self.mon_scan_p = max(0.0, self.mon_scan_p - dt * 3.0)
            return
        self.mon_scan_p = min(self.mon_need, self.mon_scan_p + dt)
        if self.mon_scan_p >= self.mon_need:
            self.open_monitor(hit)
            self.mon_scan_p = 0.0
            self.mon_hold_pos = None

    def monitor_signal(self, o):
        t = self.session_t
        base = 0.5 + 0.30 * math.sin(t * 0.85 + o.seed * 0.013) + \
               0.14 * math.sin(t * 2.3 + o.seed * 0.041)
        if o.kind == "star" and o.variable:
            base -= o.dim_amount(self.game_hours) * 0.7
        if o.kind == "anomaly":
            pulse = 0.5 + 0.5 * math.sin(t * 3.0 + o.seed)
            if o.trait == "flicker" and math.sin(t * 2.4 + o.seed) < -0.45:
                pulse *= 0.3
            base = base * 0.35 + pulse * 0.65
        base += random.uniform(-0.05, 0.05)
        return clamp(base, 0.0, 1.0)

    def open_monitor(self, o):
        for m in self.monitors:
            if m["oid"] == o.oid:
                m["flash"] = 1.0
                self.monitors.remove(m)
                self.monitors.append(m)
                return
        if len(self.monitors) >= MONITOR_SLOTS:
            old = self.monitors.pop(0)
            oo = self.world.by_id.get(old["oid"])
            if oo:
                self.log_add("MONITOR LINK DROPPED: %s (slot needed)" % oo.name,
                             PHOS_DIM, CAT_SYS)
        label = o.name if (o.kind != "anomaly" or o.stage >= 1) else "UNIDENTIFIED CONTACT"
        self.monitors.append({"oid": o.oid, "hist": [], "flash": 1.0, "sample_t": 0.0})
        self.log_add("MONITOR LINK ESTABLISHED: %s" % label, CYAN, CAT_SYS, o.oid)
        self.audio.play(self.audio.s_lock, 0.55)
        self.toast = "MONITORING: %s" % label
        self.toast_t = 2.2

    def close_monitor(self, oid):
        before = len(self.monitors)
        self.monitors = [m for m in self.monitors if m["oid"] != oid]
        if len(self.monitors) != before:
            self.audio.play(self.audio.s_ui, 0.4)

    def update_monitors(self, dt):
        if not self.monitors:
            return
        alive = []
        for m in self.monitors:
            if m["oid"] not in self.world.by_id:
                continue
            m["flash"] = max(0.0, m["flash"] - dt * 2.0)
            m["sample_t"] += dt
            if m["sample_t"] >= MONITOR_SAMPLE_DT:
                m["sample_t"] = 0.0
                o = self.world.by_id[m["oid"]]
                m["hist"].append(self.monitor_signal(o))
                if len(m["hist"]) > MONITOR_HIST_LEN:
                    del m["hist"][0]
            alive.append(m)
        self.monitors = alive

    # ---- scan resolution --------------------------------------------------
    def complete_scan(self, o):
        pan = clamp(self.world_to_screen(o.ra, o.dec)[0] / self.L.w, 0, 1)
        # codex unlock -- per-class, never per-object
        if o.kind == "star":
            self.codex_seen.add("cat:star")
        elif o.kind == "anomaly":
            if o.name in CODEX_ANOMALY:
                self.codex_seen.add("anom:" + o.name)
        else:
            if o.kind in CODEX_CELESTIAL:
                self.codex_seen.add("cat:" + o.kind)

        tool = self.tool

        if o.kind == "star":
            if o.variable and o.stage >= 2 and o.is_dimmed(self.game_hours):
                if tool != "PHOTO":
                    self.log_add(
                        "DIP DETECTED [%s] -- tool mismatch. Photometer (8) required to solve." % o.name,
                        AMBER, CAT_ANOM, o.oid)
                    self.audio.play(self.audio.s_deny, 0.6, pan)
                else:
                    o.stage = 3
                    self.score += 120
                    self.stats["resolved"] += 1
                    self.log_add("DIM CYCLE SOLVED [%s]: %s" % (o.name, o.cause),
                                 AMBER, CAT_ANOM, o.oid)
                    self.audio.play(self.audio.s_resolve, 0.9, pan)
            elif o.stage < 2:
                o.stage = 2
                pts = 10 if o.proc else 40
                self.score += pts
                self.stats["stars"] += 1
                extra = ""
                if o.variable:
                    extra = "  -- periodic dimming detected, rescan with PHOTO during a dip"
                spec = ""
                if tool == "SPECTRO" and o.note:
                    spec = "  [spectral class %s confirmed]" % o.note
                self.log_add("CATALOGUED: %s  %s  %s%s%s" %
                             (o.name, o.distance_text(),
                              "class " + (o.note or "?"), extra, spec),
                             PHOS, CAT_STAR, o.oid)
                self.audio.play(self.audio.s_lock, 0.8, pan)
        elif o.kind == "anomaly":
            if o.stage == 0:
                o.stage = 1
                o.stage_time = self.game_hours
                self.score += 90
                self.stats["anom"] += 1
                tag = (" near %s" % o.note) if o.note and o.note not in ("transient", "debug", "cheat", "chain") else ""
                self.log_add("ANOMALY CLASSIFIED [%s]%s: %s" % (o.kind, tag, o.blurb),
                             AMBER, CAT_ANOM, o.oid)
                self.log_add("   second pass available in ~3h to resolve this contact.",
                             AMBER_DIM, CAT_ANOM, o.oid)
                self.audio.play(self.audio.s_anom, 0.9, pan)

                if o.chain:
                    self.chain_anoms_scanned += 1
                elif not o.spawn:
                    self.norm_anoms_scanned += 1
                elif o.note not in ("transient", "debug", "cheat"):
                    self.norm_anoms_scanned += 1

                if (self.noticing_stage == 0
                        and self.norm_anoms_scanned >= 3
                        and self.chain_anoms_scanned >= 1):
                    self.noticing_stage = 1
                    self.noticing_oid = o.oid
                    if self.last_slot is not None:
                        try:
                            self.save_game(self.last_slot)
                        except Exception:
                            pass
                    self.begin_notice_approach()
            elif o.stage == 1:
                o.stage = 2
                self.score += 160
                self.stats["resolved"] += 1
                t = next((t for t in ANOMALY_TYPES if t["kind"] == o.kind), None)
                self.log_add("ANOMALY RESOLVED [%s]: %s" %
                             (o.kind, t["resolve"] if t else "resolved."),
                             AMBER, CAT_ANOM, o.oid)
                self.audio.play(self.audio.s_resolve, 1.0, pan)
        else:
            o.stage = 2
            pts = 80 if o.kind in ("quasar", "exotic") else (60 if not o.proc else 20)
            self.score += pts
            self.stats["deep"] += 1
            desc = o.blurb or self.proc_blurb(o)
            extra = ""
            if tool == "RANGE" and o.dist_ly is not None:
                extra = "  [ranging: %.2f ly]" % o.dist_ly
            elif tool == "POLARI" and o.kind == "exotic":
                extra = "  [polarisation: linear, 4.1%%]"
            elif tool == "INTERF" and o.kind == "galaxy":
                extra = "  [interferometric resolution: spiral arms resolved]"
            self.log_add("CATALOGUED: %s  [%s]  z=%.4f  %s -- %s%s" %
                         (o.name, o.kind.upper(), o.z, o.distance_text(), desc, extra),
                         CYAN if o.kind != "quasar" else VIOLET, CAT_STAR, o.oid)
            self.audio.play(self.audio.s_lock, 0.8, pan)

        self.maybe_cluster(o)
        self.check_milestones()

    def check_milestones(self):
        for key, thresh, msg in MILESTONES:
            tag = "%s:%d" % (key, thresh)
            if tag in self.milestones_done:
                continue
            if self.stats.get(key, 0) >= thresh:
                self.milestones_done.add(tag)
                self.score += 25
                self.toast = "MILESTONE -- %s" % msg
                self.toast_t = 3.5
                self.log_add("MILESTONE: %s  +25" % msg, CYAN, CAT_SYS)
                self.audio.play(self.audio.s_resolve, 0.65)

    def proc_blurb(self, o):
        lb = lookback_gyr(max(o.z, 0.0001))
        return ("light left this object %.2f Gyr ago; the universe was %.0f%% its present size then"
                % (lb, scale_factor(max(o.z, 0.0001)) * 100))

    def maybe_cluster(self, o):
        cell = self.world.cell(o.ra, o.dec)
        n = self.world.attention.get(cell, 0) + 1
        self.world.attention[cell] = n
        if n >= 4 and n % 3 == 1 and random.random() < 0.6:
            ra = (o.ra + random.gauss(0, 2.0)) % 360
            dec = clamp(o.dec + random.gauss(0, 2.0), -88, 88)
            a = self.world.spawn_anomaly(ra, dec, o.z, self.game_hours,
                                         note=o.name, chain=True)
            self.chain_markers.append({"oid": a.oid, "name": a.kind,
                                       "parent": o.name, "born": self.game_hours})
            self.log_add("SECONDARY CONTACT resolving near %s. It was not there before."
                         % o.name, AMBER, CAT_ANOM, a.oid)
            self.audio.play(self.audio.s_anom, 0.6)

    # ================================================================ RENDER
    def render(self):
        self.screen.fill(BG)
        if self.state == "MENU":
            self.render_menu()
        elif self.state == "BOOT":
            self.render_boot()
        elif self.state == "HORROR":
            self.render_sky_simple()
            self.render_crt()
            pygame.display.flip()
            return
        else:
            self.render_sky()
            self.render_target_markers()
            self.render_notice_marker()
            self.render_second_reticle()
            self.render_hud()
            if self.L.panel_open:
                self.render_panel()
            self.render_bottom()
            self.render_monitors()
            self.render_reticle()
            if self.finder_open:
                self.render_finder_chart()
            if self.codex_open:
                self.render_codex()
            if self.radial_open:
                self.render_radial_menu()
            if self.state == "PAUSE":
                self.render_pause()
            if self.debug_unlocked and self.debug_open:
                self.render_debug()
            if self.cheat_unlocked and self.cheat_open:
                self.render_cheat()
        self.render_crt()
        pygame.display.flip()

    def render_boot(self):
        n = min(len(BOOT_LINES), int(self.boot_t / 0.16))
        y = int(self.L.h * 0.22)
        lines = list(BOOT_LINES)
        if self.noticing_stage == 2:
            for i, ln in enumerate(lines):
                if ln.startswith("DISH SERVO"):
                    lines[i] = "DISH SERVO ............... OK (compensating)"
                    break
        for i in range(n):
            line = lines[i]
            col = AMBER if line.startswith(">") else PHOS
            text_at(self.screen, self.fonts["sm"], line,
                    (int(self.L.w * 0.18), y), col)
            y += int(22 * self.L.scale)
        if n >= len(lines) and int(self.boot_t * 2) % 2 == 0:
            text_at(self.screen, self.fonts["sm"], "_",
                    (int(self.L.w * 0.18), y), AMBER)
        text_at(self.screen, self.fonts["xs"], "press space",
                (int(self.L.w * 0.18), self.L.h - 60), PHOS_DIM)

    # ---- sky --------------------------------------------------------------
    def visible_bounds(self):
        k = max(0.08, math.cos(math.radians(self.cam_dec)))
        half_ra = (self.L.w * 0.5) / (self.zoom * k) + 2
        half_dec = (self.L.sky.h * 0.5) / self.zoom + 2
        return half_ra, half_dec

    def render_sky_simple(self):
        self.render_deep_background()

    def render_sky(self):
        clip = self.screen.get_clip()
        self.screen.set_clip(self.L.sky)
        half_ra, half_dec = self.visible_bounds()
        self.render_deep_background()

        cells = self.world.visible_cells(self.cam_ra - half_ra, self.cam_ra + half_ra,
                                         self.cam_dec - half_dec, self.cam_dec + half_dec)
        if half_ra >= 180:
            cells = list(self.world.grid.values())

        mouse = pygame.mouse.get_pos()
        mag_limit = clamp(3.4 + 3.3 * math.log10(max(self.zoom, 1.1)), 3.4, 24.0)
        drawn = 0
        for cell in cells:
            for o in cell:
                if not self.debug_reveal:
                    if o.proc:
                        if o.kind == "star":
                            if o.mag > mag_limit and o.stage < 2:
                                continue
                        elif self.zoom < 3.0 and o.stage < 2:
                            continue
                    st = self.band_strength(o)
                    if st < 0.07:
                        continue
                else:
                    st = max(self.band_strength(o), 0.55)
                x, y = self.world_to_screen(o.ra, o.dec)
                if not (-60 <= x <= self.L.w + 60 and
                        self.L.sky.top - 60 <= y <= self.L.sky.bottom + 60):
                    continue
                drawn += 1
                if o.kind == "star":
                    self.draw_star(o, x, y, st)
                elif o.kind == "anomaly":
                    self.draw_anomaly(o, x, y, st, mouse)
                else:
                    self.draw_deep(o, x, y, st)
        self.visible_count = drawn

        if self.dupe:
            o, t, off = self.dupe
            x, y = self.world_to_screen(o.ra, o.dec)
            a = clamp(t / 1.2, 0, 1)
            if a > 0.05:
                r = clamp((7.5 - o.mag) * 0.6, 1.0, 5.0)
                s = glow_sprite(int(r), dim_color(o.color, 0.8))
                s.set_alpha(int(220 * a))
                self.screen.blit(s, (x + off[0] - s.get_width() // 2,
                                     y + off[1] - s.get_height() // 2),
                                 special_flags=pygame.BLEND_RGBA_ADD)

        self.render_sun_glare()
        self.screen.set_clip(clip)

    def render_target_markers(self):
        cx = self.L.w * 0.5
        cy = self.L.sky.centery
        pad = 18 * self.L.scale

        for m in self.dim_markers + self.chain_markers:
            o = self.world.by_id.get(m["oid"])
            if o is None:
                continue
            is_dim = m in self.dim_markers
            x, y = self.world_to_screen(o.ra, o.dec)
            on_screen = (0 <= x <= self.L.w
                         and self.L.sky.top <= y <= self.L.sky.bottom)
            col = AMBER if is_dim else CYAN

            if on_screen:
                pulse = 0.7 + 0.3 * math.sin(self.session_t * 3.4)
                r = int((14 + 5 * pulse) * self.L.scale)
                pygame.draw.circle(self.screen, col, (int(x), int(y)), r, 1)
                pygame.draw.circle(self.screen, dim_color(col, 0.5),
                                   (int(x), int(y)), int(r * 1.6), 1)
            else:
                ang = math.atan2(y - cy, x - cx)
                ex, ey = self._edge_point(cx, cy, ang, pad)
                tip = (ex + math.cos(ang) * 9 * self.L.scale,
                       ey + math.sin(ang) * 9 * self.L.scale)
                la = ang + 2.5
                ra = ang - 2.5
                a1 = (ex + math.cos(la) * 8 * self.L.scale,
                      ey + math.sin(la) * 8 * self.L.scale)
                a2 = (ex + math.cos(ra) * 8 * self.L.scale,
                      ey + math.sin(ra) * 8 * self.L.scale)
                pygame.draw.polygon(self.screen, col, [tip, a1, a2], 0)
                bearing = int((math.degrees(ang) + 90) % 360)
                text_at(self.screen, self.fonts["xs"], "%03d" % bearing,
                        (ex, ey + 10 * self.L.scale), col, align="center", glow=False)

    def render_notice_marker(self):
        approaching = getattr(self, "notice_approach_t", -1.0) >= 0.0
        revealing = self.notice_reveal_t >= 0.0
        if not (approaching or revealing):
            return
        oid = self.notice_target_oid if approaching else self.noticing_oid
        if oid is None:
            return
        o = self.world.by_id.get(oid)
        if o is None:
            return

        cx = self.L.w * 0.5
        cy = self.L.sky.centery
        pad = 18 * self.L.scale
        col = RED_WARN
        x, y = self.world_to_screen(o.ra, o.dec)
        on_screen = (0 <= x <= self.L.w
                     and self.L.sky.top <= y <= self.L.sky.bottom)

        if on_screen:
            pulse = 0.6 + 0.4 * math.sin(self.session_t * 7.0)
            r = int((16 + 9 * pulse) * self.L.scale)
            pygame.draw.circle(self.screen, col, (int(x), int(y)), r, 2)
            pygame.draw.circle(self.screen, dim_color(col, 0.45),
                               (int(x), int(y)), int(r * 1.8), 1)
            for ax, ay in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                x0 = x + ax * r * 1.4
                y0 = y + ay * r * 1.4
                x1 = x + ax * r * 0.6
                y1 = y + ay * r * 0.6
                pygame.draw.line(self.screen, col, (x0, y0), (x1, y1), 2)
        else:
            ang = math.atan2(y - cy, x - cx)
            ex, ey = self._edge_point(cx, cy, ang, pad)
            tip = (ex + math.cos(ang) * 10 * self.L.scale,
                   ey + math.sin(ang) * 10 * self.L.scale)
            la, ra_ = ang + 2.5, ang - 2.5
            a1 = (ex + math.cos(la) * 9 * self.L.scale,
                  ey + math.sin(la) * 9 * self.L.scale)
            a2 = (ex + math.cos(ra_) * 9 * self.L.scale,
                  ey + math.sin(ra_) * 9 * self.L.scale)
            pygame.draw.polygon(self.screen, col, [tip, a1, a2], 0)

        if approaching:
            text_at(self.screen, self.fonts["sm"], "LOCKING...",
                    (cx, self.L.sky.top + int(20 * self.L.scale)),
                    col, align="center")

    def _edge_point(self, cx, cy, ang, pad):
        sky = self.L.sky
        dx, dy = math.cos(ang), math.sin(ang)
        ts = []
        if dx > 1e-6:
            ts.append((sky.right - pad - cx) / dx)
        if dx < -1e-6:
            ts.append((sky.left + pad - cx) / dx)
        if dy > 1e-6:
            ts.append((sky.bottom - pad - cy) / dy)
        if dy < -1e-6:
            ts.append((sky.top + pad - cy) / dy)
        ts = [t for t in ts if t > 0]
        t = min(ts) if ts else 0
        return cx + dx * t, cy + dy * t

    def render_deep_background(self):
        key = (int(self.cam_ra * 2), int(self.cam_dec * 2), self.L.w, self.L.sky.h)
        if getattr(self, "_bgfield_key", None) != key:
            rnd = random.Random(key[0] * 7919 + key[1])
            self._bgfield_pts = [(rnd.randint(0, self.L.w),
                                  rnd.randint(self.L.sky.top, self.L.sky.bottom),
                                  rnd.randint(24, 70)) for _ in range(90)]
            self._bgfield_key = key
        for x, y, b in self._bgfield_pts:
            self.screen.set_at((x, y), (b, b, b))

        if self.z_dial > 200:
            f = clamp((self.z_dial - 200) / 800.0, 0, 1)
            big = self._cmb_surface()
            big.set_alpha(int(200 * f))
            self.screen.blit(big, (0, self.L.sky.top))

    def _cmb_surface(self):
        key = (self.L.w, self.L.sky.h)
        if getattr(self, "_cmb_key", None) == key:
            return self._cmb
        s = pygame.Surface((self.L.w // 6, self.L.sky.h // 6))
        for j in range(s.get_height()):
            for i in range(s.get_width()):
                n = (math.sin(i * 0.7 + j * 0.3) + math.sin(i * 0.23 - j * 0.41) +
                     math.sin((i + j) * 0.11) + math.sin(i * 0.05 - j * 0.09) * 1.4)
                v = int(clamp(66 + n * 22, 0, 255))
                s.set_at((i, j), (int(v * 0.32), int(v * 0.48), int(v * 0.92)))
        self._cmb = pygame.transform.smoothscale(s, (self.L.w, self.L.sky.h))
        self._cmb_key = key
        return self._cmb

    def render_sun_glare(self):
        sra, sdec = self.sun_pos()
        x, y = self.world_to_screen(sra, sdec)
        if not (-40 < x < self.L.w + 40 and self.L.sky.top - 40 < y < self.L.sky.bottom + 40):
            return
        blit_glow(self.screen, (int(x), int(y)), 7, (255, 228, 170))
        pygame.draw.circle(self.screen, (255, 245, 210), (int(x), int(y)), 3)
        if self.solar_noise(sra, sdec) > 0.02:
            text_at(self.screen, self.fonts["xs"], "SOL",
                    (x + 14, y - 8), AMBER_DIM, glow=False)

    # ---- object glyphs ----------------------------------------------------
    def draw_star(self, o, x, y, st):
        dim = o.dim_amount(self.game_hours)
        b = st * (1 - dim)
        r = clamp((7.6 - o.mag) * 0.52, 0.6, 5.4) * \
            clamp(0.75 + math.log10(max(self.zoom, 1.1)) * 0.45, 0.6, 1.7)
        col = dim_color(lerp_color(o.color, (10, 10, 12), dim * 0.8),
                        clamp(b, 0.08, 1))
        if r < 1.6 or o.mag > 7.5:
            self.screen.fill(col, (int(x), int(y), max(1, int(r)), max(1, int(r))))
        else:
            blit_glow(self.screen, (int(x), int(y)), int(r), col)
        if o.variable and o.stage >= 2:
            if o.is_dimmed(self.game_hours) and o.stage < 3:
                ring = RED_WARN
                pygame.draw.circle(self.screen, ring, (int(x), int(y)),
                                   int(r + 10 * self.L.scale), 2)
                pulse = 0.6 + 0.4 * math.sin(self.session_t * 4.0)
                pygame.draw.circle(self.screen, dim_color(RED_WARN, pulse),
                                   (int(x), int(y)),
                                   int(r + 16 * self.L.scale + pulse * 4), 1)
                text_at(self.screen, self.fonts["xs"], "DIP IN PROGRESS",
                        (x + r + 8, y - 20), RED_WARN, glow=True)
            else:
                pygame.draw.circle(self.screen, AMBER_DIM, (int(x), int(y)),
                                   int(r + 7 * self.L.scale), 1)
        show_label = (o.stage >= 2) or (not o.proc and self.zoom > 7) or self.zoom > 60
        if show_label and b > 0.3:
            mark = ""
            if o.stage >= 2:
                mark = "  *" if not o.variable else \
                    ("  [SOLVED]" if o.stage >= 3 else "  [VARIABLE]")
            text_at(self.screen, self.fonts["xs"], o.name + mark,
                    (x + r + 6, y - 7), PHOS if o.stage >= 2 else PHOS_DIM,
                    alpha=int(clamp(b, 0, 1) * 230), glow=o.stage >= 2)

    def draw_deep(self, o, x, y, st):
        col = dim_color(o.color, clamp(st, 0.1, 1))
        s = clamp(6.5 - (o.mag - 8) * 0.35, 3.0, 11.0) * self.L.scale
        k = o.kind
        if k == "galaxy":
            rect = pygame.Rect(0, 0, int(s * 2.2), int(s * 1.1))
            rect.center = (int(x), int(y))
            pygame.draw.ellipse(self.screen, col, rect, 1)
            pygame.draw.ellipse(self.screen, col, rect.inflate(-s, -s * 0.6))
        elif k == "quasar":
            pygame.draw.circle(self.screen, col, (int(x), int(y)), 2)
            for a in (0, math.pi / 2, math.pi, 3 * math.pi / 2):
                pygame.draw.line(self.screen, col, (x, y),
                                 (x + math.cos(a) * s * 1.6,
                                  y + math.sin(a) * s * 1.6), 1)
        elif k == "nebula":
            blit_glow(self.screen, (int(x), int(y)), int(s * 0.7), col)
            pygame.draw.circle(self.screen, col, (int(x), int(y)), int(s * 1.3), 1)
        elif k == "globular":
            pygame.draw.circle(self.screen, col, (int(x), int(y)), int(s), 1)
            for i in range(6):
                a = i * 1.047 + self.session_t * 0.1
                pygame.draw.circle(self.screen, col,
                                   (int(x + math.cos(a) * s * 0.5),
                                    int(y + math.sin(a) * s * 0.5)), 1)
        elif k == "open":
            for i in range(5):
                a = i * 1.257
                pygame.draw.circle(self.screen, col,
                                   (int(x + math.cos(a) * s),
                                    int(y + math.sin(a) * s)), 1)
        elif k == "remnant":
            pygame.draw.circle(self.screen, col, (int(x), int(y)), int(s), 1)
            pygame.draw.circle(self.screen, dim_color(col, 0.5),
                               (int(x), int(y)), int(s * 0.55), 1)
        elif k == "exotic":
            pygame.draw.circle(self.screen, col, (int(x), int(y)), int(s * 0.7), 1)
            pygame.draw.line(self.screen, col, (x - s * 1.5, y), (x + s * 1.5, y), 1)
            pygame.draw.line(self.screen, col, (x, y - s * 1.5), (x, y + s * 1.5), 1)
        elif k == "cluster":
            for dx in (-1, 1):
                for dy in (-1, 1):
                    pygame.draw.line(self.screen, col, (x + dx * s, y + dy * s),
                                     (x + dx * s * 0.4, y + dy * s), 1)
                    pygame.draw.line(self.screen, col, (x + dx * s, y + dy * s),
                                     (x + dx * s, y + dy * s * 0.4), 1)
        else:
            pygame.draw.rect(self.screen, col, (x - s, y - s, s * 2, s * 2), 1)

        if (not o.proc and self.zoom > 3.5) or o.stage >= 2 or self.zoom > 40:
            lab = o.name if (o.stage >= 2 or not o.proc) else "?"
            text_at(self.screen, self.fonts["xs"], lab, (x + s * 1.8, y - 7),
                    col if o.stage >= 2 else dim_color(col, 0.7),
                    alpha=int(clamp(st, 0, 1) * 220), glow=False)

    def draw_anomaly(self, o, x, y, st, mouse):
        t = self.session_t
        if o.trait == "edge":
            d = math.hypot(x - mouse[0], y - mouse[1])
            fade = clamp((d - 120 * self.L.scale) / (90 * self.L.scale), 0, 1)
            if fade <= 0.02 and o.stage < 2:
                return
            st *= (fade if o.stage < 2 else 1.0)
        if o.trait == "flicker" and o.stage < 2:
            if math.sin(t * 2.4 + o.seed) < -0.45:
                return
        pulse = 0.72 + 0.28 * math.sin(t * 3.0 + o.seed)
        col = AMBER if o.stage >= 1 else AMBER_DIM
        if o.note == "transient" and o.stage == 0:
            col = RED_WARN
        elif o.chain and o.stage < 2:
            col = CYAN
        col = dim_color(col, clamp(st, 0.15, 1))
        size = (6 + 2 * pulse) * self.L.scale
        draw_reticle(self.screen, (x, y), size + 5 * self.L.scale, col,
                     rot=t * 0.6, gap=0.5, width=1)
        draw_diamond(self.screen, (x, y), size * 0.55, col, filled=o.stage >= 2)
        if o.stage >= 1:
            lab = o.kind + ("" if o.stage >= 2 else "  [UNRESOLVED]")
            if o.chain and o.stage < 2:
                lab += "  [CHAIN]"
            text_at(self.screen, self.fonts["xs"], lab, (x + 11, y - 7), col, glow=False)
        elif self.zoom > 5:
            text_at(self.screen, self.fonts["xs"], "??", (x + 11, y - 7), col, glow=False)

    # ---- reticle ----------------------------------------------------------
    def render_reticle(self):
        if self.state != "PLAY":
            return
        mouse = pygame.mouse.get_pos()
        if not self.L.sky.collidepoint(mouse):
            return
        if self.L.panel_open and self.L.panel.collidepoint(mouse):
            return
        if self.monitor_hit(mouse) or self.debug_hit(mouse) or self.cheat_hit(mouse):
            return
        if self.codex_open:
            return
        if self.monitor_mode:
            self.render_reticle_monitor(mouse)
            return
        o = self.target
        col = MODE_COLORS[self.mode]
        if o is not None:
            col = PHOS_DIM if self.obj_done(o) else (AMBER if o.kind == "anomaly" else col)
        R = int(16 * self.L.scale)
        draw_reticle(self.screen, mouse, R, col, rot=self.session_t * 0.5)
        pygame.draw.line(self.screen, col, (mouse[0] - 4, mouse[1]),
                         (mouse[0] + 4, mouse[1]), 1)
        pygame.draw.line(self.screen, col, (mouse[0], mouse[1] - 4),
                         (mouse[0], mouse[1] + 4), 1)

        sig = self.signal_strength(mouse)
        bw, bh = int(52 * self.L.scale), int(4 * self.L.scale)
        bx, by = mouse[0] - bw // 2, mouse[1] - R - int(14 * self.L.scale)
        pygame.draw.rect(self.screen, PHOS_FAINT, (bx, by, bw, bh), 1)
        if sig > 0.02:
            c = lerp_color(PHOS_DIM, AMBER, sig)
            pygame.draw.rect(self.screen, c, (bx + 1, by + 1,
                                              int((bw - 2) * sig), bh - 2))

        if self.tool:
            tc = TOOL_COLORS[self.tool]
            text_at(self.screen, self.fonts["xs"], self.tool,
                    (mouse[0], mouse[1] + R + int(6 * self.L.scale)),
                    tc, align="center", glow=True)

        if self.interference:
            text_at(self.screen, self.fonts["sm"], "NO CARRIER",
                    (mouse[0] + 24, mouse[1] + 16), RED_WARN)
            return

        if o is not None:
            need = self.scan_requirement(o)
            if self.scan_p > 0:
                frac = clamp(self.scan_p / need, 0, 1)
                rect = pygame.Rect(0, 0, R * 2 + 14, R * 2 + 14)
                rect.center = mouse
                pygame.draw.arc(self.screen, AMBER, rect, -math.pi / 2,
                                -math.pi / 2 + frac * 2 * math.pi, 3)
                self.render_spectrometer(o)
            text_at(self.screen, self.fonts["sm"], self.describe(o),
                    (mouse[0] + 24, mouse[1] + 16),
                    AMBER if self.scan_p > 0 else PHOS_DIM)

    def render_reticle_monitor(self, mouse):
        o = self.mon_target
        already = o is not None and any(m["oid"] == o.oid for m in self.monitors)
        col = PHOS_DIM if already else CYAN
        R = int(16 * self.L.scale)
        draw_diamond(self.screen, mouse, int(R * 0.55), col, filled=False, width=2)
        draw_reticle(self.screen, mouse, R, col, rot=-self.session_t * 0.6,
                     gap=0.6, width=1)
        text_at(self.screen, self.fonts["xs"], "M",
                (mouse[0], mouse[1] - R - int(15 * self.L.scale)),
                col, align="center")

        if self.interference:
            text_at(self.screen, self.fonts["sm"], "NO CARRIER",
                    (mouse[0] + 24, mouse[1] + 16), RED_WARN)
            return

        if o is not None:
            if self.mon_scan_p > 0 and not already:
                frac = clamp(self.mon_scan_p / self.mon_need, 0, 1)
                rect = pygame.Rect(0, 0, R * 2 + 14, R * 2 + 14)
                rect.center = mouse
                pygame.draw.arc(self.screen, CYAN, rect, -math.pi / 2,
                                -math.pi / 2 + frac * 2 * math.pi, 3)
            label = o.name if (o.kind != "anomaly" or o.stage >= 1) else "UNIDENTIFIED CONTACT"
            msg = ("%s -- already monitoring" % label if already
                   else "%s -- hold to MONITOR" % label)
            text_at(self.screen, self.fonts["sm"], msg,
                    (mouse[0] + 24, mouse[1] + 16),
                    PHOS_DIM if already else CYAN)
        else:
            text_at(self.screen, self.fonts["sm"], "MONITOR SCAN -- aim at a contact",
                    (mouse[0] + 24, mouse[1] + 16), PHOS_DIM)

    def describe(self, o):
        if self.obj_done(o):
            if o.kind == "anomaly":
                return "%s -- resolved" % o.kind
            return "%s -- catalogued" % o.name
        if o.kind == "anomaly":
            if o.stage == 1:
                left = 3.0 - (self.game_hours - o.stage_time)
                if left > 0:
                    return "%s -- classified, second pass in %.1fh" % (o.kind, left)
                return "%s -- hold to RESOLVE" % o.kind
            band = "" if self.mode_match(o) else "  (wrong band: %s)" % o.band
            tag = "  [CHAIN]" if o.chain else ""
            return "UNKNOWN CONTACT -- hold to scan%s%s" % (band, tag)
        if o.kind == "star" and o.variable and o.stage >= 2 and o.is_dimmed(self.game_hours):
            if self.tool != "PHOTO":
                return "%s -- LUMINOSITY DROP -- switch to PHOTO (8) to solve" % o.name
            return "%s -- LUMINOSITY DROP -- hold to investigate" % o.name
        band = "" if self.mode_match(o) else "  (weak on %s; try %s)" % (self.mode, o.band)
        return "%s -- %s -- hold to scan%s" % (o.name, o.distance_text(), band)

    def render_spectrometer(self, o):
        w = int(clamp(self.L.w * 0.30, 280, 430))
        h = int(96 * self.L.scale)
        x = 14
        y = self.L.sky.bottom - h - 10
        rect = pygame.Rect(x, y, w, h)
        panel_rect(self.screen, rect)
        match = self.mode_match(o)
        head = "SPECTROMETER  //  %s  //  %s" % \
               (self.mode, o.name if o.kind != "anomaly" else "CONTACT")
        text_at(self.screen, self.fonts["xs"], head, (x + 8, y + 6), PHOS_DIM, glow=False)

        gx, gy = x + 8, y + 26
        gw, gh = w - 16, h - 40
        pygame.draw.rect(self.screen, PHOS_FAINT, (gx, gy, gw, gh), 1)

        z = max(0.0, o.z)
        pts = []
        amp = gh * (0.30 if match else 0.10)
        for i in range(0, gw, 2):
            f = i / gw
            v = math.sin(f * 26 + self.spectrum_phase) * 0.35
            v += math.sin(f * 61 - self.spectrum_phase * 1.7) * 0.18
            v += random.uniform(-0.22, 0.22) * (0.5 if match else 1.4)
            if match:
                for _, rest, _c in SPECTRAL_LINES:
                    obs = rest * (1 + z)
                    lf = (math.log10(max(obs, 1)) - 1.9) / 2.6
                    if 0 <= lf <= 1:
                        v += math.exp(-((f - lf) * 44) ** 2) * 1.5
            pts.append((gx + i, gy + gh * 0.5 - v * amp))
        if len(pts) > 1:
            pygame.draw.lines(self.screen,
                              MODE_COLORS[self.mode] if match else PHOS_FAINT,
                              False, pts, 1)
        if match:
            for nm, rest, c in SPECTRAL_LINES[::2]:
                obs = rest * (1 + z)
                lf = (math.log10(max(obs, 1)) - 1.9) / 2.6
                if 0 <= lf <= 1:
                    lx = gx + lf * gw
                    pygame.draw.line(self.screen, c, (lx, gy), (lx, gy + gh), 1)
            ha = 656.28 * (1 + z)
            text_at(self.screen, self.fonts["xs"],
                    "H-alpha 656nm -> %.0f nm  [%s]   z=%.4f" %
                    (ha, band_label(ha), z),
                    (gx, y + h - 16), PHOS_DIM, glow=False)
        else:
            text_at(self.screen, self.fonts["xs"],
                    "NO RETURN ON %s -- this contact answers on %s" % (self.mode, o.band),
                    (gx, y + h - 16), RED_WARN, glow=False)

    # ---- monitor windows --------------------------------------------------
    def render_monitors(self):
        if not self.monitors:
            return
        L = self.L
        w = int(clamp(L.w * 0.155, 164, 220))
        h = int(94 * L.scale)
        gap = int(8 * L.scale)
        x = 12
        y = L.top_h + int(10 * L.scale)
        spokes = (("VISUAL", -math.pi / 2), ("THERMAL", math.pi / 2 - 0.95),
                  ("RADIO", math.pi / 2 + 0.95))
        for m in self.monitors:
            o = self.world.by_id.get(m["oid"])
            if o is None:
                m["rect"] = None
                continue
            rect = pygame.Rect(x, y, w, h)
            m["rect"] = rect
            flash = m.get("flash", 0.0)
            border = lerp_color(CYAN, WHITE_STAR, flash) if flash > 0 else CYAN
            panel_rect(self.screen, rect, border=border, fill=(0, 16, 20, 195))

            label = o.name if (o.kind != "anomaly" or o.stage >= 1) else "UNIDENTIFIED"
            if len(label) > 20:
                label = label[:19] + "."
            text_at(self.screen, self.fonts["xs"], label,
                    (rect.x + 6, rect.y + 4), CYAN, glow=False)

            close_rect = pygame.Rect(rect.right - int(16 * L.scale), rect.y + 3,
                                     int(12 * L.scale), int(12 * L.scale))
            m["close_rect"] = close_rect
            pygame.draw.rect(self.screen, PHOS_FAINT, close_rect, 1)
            text_at(self.screen, self.fonts["xs"], "x", close_rect.center, PHOS_DIM,
                    align="center", glow=False)

            gx, gy = rect.x + 6, rect.y + 19
            gw, gh = rect.w - 12, int(38 * L.scale)
            pygame.draw.rect(self.screen, PHOS_FAINT, (gx, gy, gw, gh), 1)
            hist = m["hist"]
            if len(hist) > 1:
                pts = [(gx + (i / max(1, MONITOR_HIST_LEN - 1)) * gw,
                        gy + gh - v * gh) for i, v in enumerate(hist)]
                pygame.draw.lines(self.screen, CYAN, False, pts, 1)
                cur = hist[-1]
                text_at(self.screen, self.fonts["xs"], "ACT %.2f" % cur,
                        (gx, gy + gh + 2), CYAN if cur > 0.5 else PHOS_DIM, glow=False)
            else:
                text_at(self.screen, self.fonts["xs"], "acquiring...",
                        (gx, gy + gh + 2), PHOS_DIM, glow=False)

            rcx = rect.right - int(24 * L.scale)
            rcy = gy + gh + int(15 * L.scale)
            rr = int(9 * L.scale)
            for name, ang in spokes:
                on_band = (name == o.band)
                length = rr * (0.95 if on_band else 0.3)
                col = MODE_COLORS[name] if on_band else PHOS_FAINT
                ex, ey = rcx + math.cos(ang) * length, rcy + math.sin(ang) * length
                pygame.draw.line(self.screen, col, (rcx, rcy), (ex, ey), 2)
                if name == self.mode:
                    pygame.draw.circle(self.screen, AMBER, (int(ex), int(ey)), 2)
            text_at(self.screen, self.fonts["xs"], "band: %s" % o.band,
                    (rect.x + 6, rect.bottom - int(13 * L.scale)), PHOS_DIM, glow=False)

            y += h + gap

    # ---- finder chart -----------------------------------------------------
    def render_finder_chart(self):
        L = self.L
        veil = pygame.Surface((L.w, L.h), pygame.SRCALPHA)
        veil.fill((0, 4, 6, 235))
        self.screen.blit(veil, (0, 0))

        cx = L.w // 2
        text_at(self.screen, self.fonts["xl"], "FINDER CHART", (cx, int(L.h * 0.06)),
                PHOS, align="center")
        text_at(self.screen, self.fonts["xs"],
                "whole sky  //  RA across, DEC down  //  0 / ESC to close",
                (cx, int(L.h * 0.06 + 44 * L.scale)),
                PHOS_DIM, align="center", glow=False)

        margin = int(60 * L.scale)
        map_rect = pygame.Rect(margin, int(L.h * 0.15),
                               L.w - margin * 2,
                               int(L.h * 0.70))
        panel_rect(self.screen, map_rect, border=PHOS_DIM, fill=(0, 10, 14, 220))

        for ra_h in range(0, 24, 2):
            x = map_rect.x + int((ra_h / 24.0) * map_rect.w)
            pygame.draw.line(self.screen, PHOS_FAINT,
                             (x, map_rect.y), (x, map_rect.bottom), 1)
            if ra_h % 4 == 0:
                text_at(self.screen, self.fonts["xs"], "%02dh" % ra_h,
                        (x, map_rect.y - int(14 * L.scale)),
                        PHOS_FAINT, align="center", glow=False)
        for d in range(-60, 61, 30):
            y = map_rect.y + int(((60 - d) / 120.0) * map_rect.h)
            pygame.draw.line(self.screen, PHOS_FAINT,
                             (map_rect.x, y), (map_rect.right, y), 1)
            text_at(self.screen, self.fonts["xs"], "%+d" % d,
                    (map_rect.x - int(8 * L.scale), y - 6),
                    PHOS_FAINT, align="right", glow=False)

        for o in self.world.objects:
            if o.stage == 0 and not self.debug_reveal:
                continue
            x = map_rect.x + int((o.ra / 360.0) * map_rect.w)
            y = map_rect.y + int(((90 - o.dec) / 180.0) * map_rect.h)
            if not map_rect.collidepoint(x, y):
                continue
            if o.kind == "anomaly":
                col = AMBER
                pygame.draw.circle(self.screen, col, (x, y), 3, 0)
            elif o.kind == "star":
                col = PHOS
                pygame.draw.circle(self.screen, col, (x, y), 1, 0)
            else:
                col = CYAN
                pygame.draw.rect(self.screen, col, (x - 1, y - 1, 3, 3), 0)

        px = map_rect.x + int((self.cam_ra / 360.0) * map_rect.w)
        py = map_rect.y + int(((90 - self.cam_dec) / 180.0) * map_rect.h)
        pygame.draw.circle(self.screen, RED_WARN, (px, py),
                           int(9 * L.scale), 2)
        pygame.draw.line(self.screen, RED_WARN,
                         (px - 14, py), (px + 14, py), 1)
        pygame.draw.line(self.screen, RED_WARN,
                         (px, py - 14), (px, py + 14), 1)
        text_at(self.screen, self.fonts["xs"], "YOU",
                (px + 14, py + 6), RED_WARN, glow=True)

        sra, sdec = self.sun_pos()
        sx = map_rect.x + int((sra / 360.0) * map_rect.w)
        sy = map_rect.y + int(((90 - sdec) / 180.0) * map_rect.h)
        if map_rect.collidepoint(sx, sy):
            blit_glow(self.screen, (sx, sy), 6, (255, 228, 170))
            pygame.draw.circle(self.screen, (255, 245, 210), (sx, sy), 3)
            text_at(self.screen, self.fonts["xs"], "SOL",
                    (sx + 8, sy - 6), AMBER, glow=False)

        ly = map_rect.bottom + int(14 * L.scale)
        lx = map_rect.x
        pygame.draw.circle(self.screen, PHOS, (lx, ly + 6), 1, 0)
        text_at(self.screen, self.fonts["xs"], "star", (lx + 8, ly), PHOS_DIM, glow=False)
        pygame.draw.rect(self.screen, CYAN, (lx + 60, ly + 5, 3, 3), 0)
        text_at(self.screen, self.fonts["xs"], "deep sky", (lx + 68, ly), PHOS_DIM, glow=False)
        pygame.draw.circle(self.screen, AMBER, (lx + 150, ly + 6), 3, 0)
        text_at(self.screen, self.fonts["xs"], "anomaly", (lx + 158, ly), PHOS_DIM, glow=False)
        pygame.draw.circle(self.screen, RED_WARN, (lx + 240, ly + 6), 6, 1)
        text_at(self.screen, self.fonts["xs"], "current pointing", (lx + 250, ly),
                PHOS_DIM, glow=False)

    # ---- radial menu ------------------------------------------------------    # ---- codex ------------------------------------------------------------
    def render_codex(self):
        L = self.L
        veil = pygame.Surface((L.w, L.h), pygame.SRCALPHA)
        veil.fill((0, 4, 6, 240))
        self.screen.blit(veil, (0, 0))

        cx = L.w // 2
        text_at(self.screen, self.fonts["xl"], "CODEX",
                (cx, int(L.h * 0.05)), PHOS, align="center")
        text_at(self.screen, self.fonts["xs"],
                "field guide  //  K or ESC closes  //  LEFT/RIGHT tabs  //  wheel scrolls",
                (cx, int(L.h * 0.05 + 40 * L.scale)),
                PHOS_DIM, align="center", glow=False)

        tabs = ["CELESTIAL", "ANOMALIES"]
        chip_w = int(clamp(L.w * 0.28, 240, 340))
        chip_h = int(24 * L.scale)
        chip_y = int(L.h * 0.05 + 70 * L.scale)
        chip_start = cx - chip_w - int(4 * L.scale)
        self.codex_rects = []
        for i, name in enumerate(tabs):
            r = pygame.Rect(chip_start + i * (chip_w + int(8 * L.scale)),
                            chip_y, chip_w, chip_h)
            active = (i == self.codex_tab)
            col = PHOS if active else PHOS_DIM
            panel_rect(self.screen, r,
                       border=col if active else PHOS_FAINT,
                       fill=(0, 26, 20, 200) if active else (0, 10, 14, 150))
            text_at(self.screen, self.fonts["xs"], name,
                    (r.centerx, r.y + int(4 * L.scale)), col,
                    align="center", glow=active)
            self.codex_rects.append((r, i))

        margin = int(60 * L.scale)
        body = pygame.Rect(margin, chip_y + chip_h + int(10 * L.scale),
                           L.w - margin * 2,
                           int(L.h * 0.74))
        panel_rect(self.screen, body, border=PHOS_DIM, fill=(0, 10, 14, 220))

        if self.codex_tab == 0:
            self._render_codex_list(body, CODEX_CELESTIAL, "cat")
        else:
            self._render_codex_list(body, CODEX_ANOMALY, "anom")

    def _render_codex_list(self, body, table, prefix):
        f = self.fonts["xs"]
        line_h = int(13 * self.L.scale)
        pad = int(12 * self.L.scale)
        row_h = line_h * 4
        prev_clip = self.screen.get_clip()
        self.screen.set_clip(body)

        cursor_y = body.y + pad - self.codex_scroll * row_h
        discovered = 0
        total = len(table)
        for name, desc in table.items():
            key = prefix + ":" + name
            seen = key in self.codex_seen
            if seen:
                discovered += 1
            if cursor_y + row_h >= body.y and cursor_y <= body.bottom:
                if seen:
                    text_at(self.screen, f, name, (body.x + pad, cursor_y),
                            PHOS, glow=True)
                    wrapped = wrap_text(desc, f, body.w - pad * 2, 2)
                    yy = cursor_y + line_h
                    for ln in wrapped:
                        text_at(self.screen, f, ln, (body.x + pad, yy),
                                PHOS_DIM, glow=False)
                        yy += line_h
                else:
                    text_at(self.screen, f, "???", (body.x + pad, cursor_y),
                            PHOS_FAINT, glow=False)
                    text_at(self.screen, f, "not yet observed",
                            (body.x + pad, cursor_y + line_h),
                            PHOS_FAINT, glow=False)
            cursor_y += row_h

        self.screen.set_clip(prev_clip)

        text_at(self.screen, f,
                "DISCOVERED  %d / %d" % (discovered, total),
                (body.right - pad, body.bottom - line_h - pad // 2),
                AMBER_DIM, align="right", glow=False)


    def render_radial_menu(self):
        L = self.L
        cx, cy = L.w * 0.5, L.sky.centery
        r_in = int(46 * L.scale)
        r_out = int(118 * L.scale)

        backdrop = pygame.Surface((L.w, L.h), pygame.SRCALPHA)
        backdrop.fill((0, 0, 0, 110))
        self.screen.blit(backdrop, (0, 0))

        slots = len(TOOLS) + 1
        seg = (math.pi * 2) / slots
        for i in range(slots):
            a0 = -math.pi / 2 + i * seg
            a1 = a0 + seg
            mid = (a0 + a1) / 2
            pts = []
            for f in (0.0, 0.25, 0.5, 0.75, 1.0):
                aa = lerp(a0, a1, f)
                pts.append((cx + math.cos(aa) * r_out,
                            cy + math.sin(aa) * r_out))
            for f in (1.0, 0.75, 0.5, 0.25, 0.0):
                aa = lerp(a0, a1, f)
                pts.append((cx + math.cos(aa) * r_in,
                            cy + math.sin(aa) * r_in))
            sel = (i == self.radial_sel)
            if i == len(TOOLS):
                base = (60, 60, 60) if not sel else PHOS_DIM
                label = "NONE"
            else:
                tname = TOOLS[i]
                base = TOOL_COLORS[tname]
                label = tname
                if self.tool == tname:
                    base = WHITE_STAR
            fill = (base[0] // 4, base[1] // 4, base[2] // 4)
            border = base if sel else PHOS_FAINT
            pygame.draw.polygon(self.screen, fill, pts)
            pygame.draw.polygon(self.screen, border, pts, 2 if sel else 1)
            tx = cx + math.cos(mid) * (r_in + (r_out - r_in) * 0.55)
            ty = cy + math.sin(mid) * (r_in + (r_out - r_in) * 0.55)
            text_at(self.screen, self.fonts["xs"], label, (tx, ty - 7),
                    base if sel else PHOS_DIM, align="center", glow=sel)

        pygame.draw.circle(self.screen, PHOS_FAINT, (cx, cy), r_in, 1)
        pygame.draw.circle(self.screen, PHOS_FAINT, (cx, cy), r_out, 1)
        text_at(self.screen, self.fonts["xs"], "TOOL",
                (cx, cy - 7), PHOS_DIM, align="center", glow=False)

    # ---- HUD --------------------------------------------------------------
    def render_hud(self):
        L = self.L
        pygame.draw.line(self.screen, PHOS_FAINT, (0, L.top_h), (L.w, L.top_h), 1)
        text_at(self.screen, self.fonts["md"], TITLE, (14, int(9 * L.scale)), PHOS)
        text_at(self.screen, self.fonts["xs"],
                "%s   SCORE %06d   stars %d  deep %d  anomalies %d (%d resolved)" %
                (self.clock_str(), self.score, self.stats["stars"], self.stats["deep"],
                 self.stats["anom"], self.stats["resolved"]),
                (L.w - 14, int(14 * L.scale)), PHOS_DIM, align="right", glow=False)

        ra, dec = self.screen_to_world(*pygame.mouse.get_pos())
        h = ra / 15.0
        tool_str = self.tool or "none"
        pos = "RA %02dh%02dm   DEC %+05.1f   FOV %.1f deg   tool %s" % (
            int(h), int((h - int(h)) * 60), dec, (L.w / self.zoom), tool_str)
        text_at(self.screen, self.fonts["xs"], pos,
                (L.w * 0.34, int(14 * L.scale)), PHOS_DIM, glow=False)

        if self.toast_t > 0:
            text_at(self.screen, self.fonts["md"], self.toast,
                    (L.w // 2, L.sky.top + 12), AMBER, align="center")
        if self.settings["hints"] and not self.interference:
            hint_h = self.fonts["xs"].get_height()
            text_at(self.screen, self.fonts["xs"], HINTS[self.hint_i],
                    (L.w // 2, L.sky.bottom - hint_h - int(6 * L.scale)),
                    PHOS_DIM, align="center", glow=False)

    def render_bottom(self):
        L = self.L
        r = L.bottom
        pygame.draw.line(self.screen, PHOS_FAINT, (0, r.top), (L.w, r.top), 1)

        self.mode_rects = []
        bx = 14
        by = r.top + int(6 * L.scale)
        for i, m in enumerate(MODES):
            bw, bh = int(96 * L.scale), int(22 * L.scale)
            rect = pygame.Rect(bx, by, bw, bh)
            active = (m == self.mode)
            col = MODE_COLORS[m]
            panel_rect(self.screen, rect, border=col if active else PHOS_FAINT,
                       fill=(col[0] // 8, col[1] // 8, col[2] // 8,
                             200 if active else 90))
            text_at(self.screen, self.fonts["xs"], "%d %s" % (i + 1, m),
                    (rect.centerx, rect.y + int(4 * L.scale)),
                    col if active else PHOS_DIM, align="center", glow=active)
            self.mode_rects.append((rect, m))
            bx += bw + 4
        mode_end = bx

        self.tool_rects = []
        hint_y = by + int(24 * L.scale)
        text_at(self.screen, self.fonts["xs"], "SENSOR", (14, hint_y),
                PHOS_DIM, glow=False)
        text_at(self.screen, self.fonts["xs"],
                "TOOLS:  4-9   or   HOLD X",
                (14 + int(62 * L.scale), hint_y), PHOS_DIM, glow=False)
        text_at(self.screen, self.fonts["xs"], "MAP:  0",
                (14 + int(210 * L.scale), hint_y), PHOS_DIM, glow=False)
        cur = self.tool or "none"
        cur_col = TOOL_COLORS.get(self.tool, PHOS_DIM) if self.tool else PHOS_DIM
        tool_label = "TOOL:  %s" % cur
        tool_x = 14 + int(276 * L.scale)
        text_at(self.screen, self.fonts["xs"], tool_label,
                (tool_x, hint_y), cur_col, glow=bool(self.tool))
        hint_right = tool_x + self.fonts["xs"].size(tool_label)[0]

        R = int(clamp(L.bottom_h * 0.30, 18, 28))
        dcx = max(mode_end, hint_right) + int(24 * L.scale) + R
        dcx = min(dcx, L.w - R - int(10 * L.scale))
        dcy = r.top + int(L.bottom_h * 0.58)
        self.dial_center = (dcx, dcy)
        self.dial_R = R
        self.dial_rect = pygame.Rect(dcx - R, dcy - R, R * 2, R * 2)

        def _dial_pt(p, rad_mul=1.0):
            ang = math.radians(lerp(-DIAL_SWEEP_DEG, DIAL_SWEEP_DEG, clamp(p, 0, 1)))
            return (dcx + math.sin(ang) * R * rad_mul, dcy - math.cos(ang) * R * rad_mul)

        pygame.draw.lines(self.screen, PHOS_FAINT, False,
                          [_dial_pt(i / 40.0) for i in range(41)], 1)
        n_fill = max(0, int(self.dial_p * 40))
        if n_fill > 1:
            fillcol = lerp_color(PHOS, RED_WARN, clamp(self.dial_p * 1.3, 0, 1))
            pygame.draw.lines(self.screen, fillcol, False,
                              [_dial_pt(i / 40.0) for i in range(n_fill + 1)], 2)
        for zt, lab in ((0.0, "0"), (0.02, ".02"), (0.16, ".16"), (1.0, "1"),
                        (7.0, "7"), (100.0, "100"), (1089.0, "CMB")):
            p = self.z_to_p(zt)
            pygame.draw.line(self.screen, PHOS_DIM, _dial_pt(p, 0.80),
                             _dial_pt(p, 1.0), 1)
        needle = _dial_pt(self.dial_p, 0.86)
        pygame.draw.line(self.screen, AMBER, (dcx, dcy), needle, 2)
        pygame.draw.circle(self.screen, AMBER, (int(dcx), int(dcy)), 3)
        pygame.draw.circle(self.screen, PHOS_FAINT, (int(dcx), int(dcy)), R, 1)
        text_at(self.screen, self.fonts["sm"], "Z", (dcx, dcy - int(7 * L.scale)),
                PHOS, align="center", glow=True)
        text_at(self.screen, self.fonts["xs"], "0  .02  .16  1  7  100  CMB",
                (dcx, dcy + R + int(3 * L.scale)), PHOS_FAINT,
                align="center", glow=False)
        text_at(self.screen, self.fonts["xs"], "Q/E / drag / scroll",
                (dcx, dcy - R - int(14 * L.scale)),
                PHOS_DIM, align="center", glow=False)

        z = self.z_dial
        rx = dcx + R + int(20 * L.scale)
        if rx < L.w - 130:
            lb = lookback_gyr(z)
            cm = comoving_mpc(z) * MPC_TO_MLY
            v = recession_kms(z)
            vfrac = v / C_KMS
            afrac = scale_factor(z)
            lines = [
                "z = %.4f" % z if z < 10 else "z = %.1f" % z,
                "lookback %.3f Gyr" % lb,
                "comoving %.1f Mly" % cm if cm < 5000 else "comoving %.2f Gly" % (cm / 1000),
                "v_rec %.0f km/s %s" % (v, bar_str(vfrac, 6)),
                "a = %.4f %s" % (afrac, bar_str(afrac, 6)),
            ]
            for i, s in enumerate(lines):
                text_at(self.screen, self.fonts["xs"], s,
                        (rx, r.top + 6 + i * int(13 * L.scale)),
                        PHOS if i == 0 else PHOS_DIM, glow=(i == 0))

    # ---- side panel -------------------------------------------------------
    def render_panel(self):
        L = self.L
        rect = L.panel
        panel_rect(self.screen, rect, fill=(0, 12, 9, 205))
        tabs = ["LOG", "DATA", "CALIB", "HELP"]
        self.tab_rects = []
        tw = rect.w // 4
        for i, name in enumerate(tabs):
            tr = pygame.Rect(rect.x + i * tw, rect.y, tw, int(24 * L.scale))
            active = (i == self.tab)
            flag = (i == 2 and self.interference and int(self.session_t * 2) % 2 == 0)
            col = RED_WARN if flag else (PHOS if active else PHOS_DIM)
            if active:
                pygame.draw.rect(self.screen, (0, 26, 20), tr)
            text_at(self.screen, self.fonts["xs"], name,
                    (tr.centerx, tr.y + int(5 * L.scale)),
                    col, align="center", glow=active)
            self.tab_rects.append((tr, i))
        pygame.draw.line(self.screen, PHOS_FAINT,
                         (rect.x, rect.y + int(24 * L.scale)),
                         (rect.right, rect.y + int(24 * L.scale)), 1)
        body = pygame.Rect(rect.x + 8, rect.y + int(30 * L.scale), rect.w - 16,
                           rect.h - int(38 * L.scale))
        self.log_rects = []
        self.help_nav_rects = []
        if self.tab == 0:
            self.render_tab_log(body)
        elif self.tab == 1:
            self.render_tab_data(body)
        elif self.tab == 2:
            self.render_tab_calib(body)
        else:
            self.render_tab_help(body)

    def render_tab_log(self, b):
        f = FILTERS[self.filter_i]
        self.filter_rect = pygame.Rect(b.x, b.y, b.w, int(18 * self.L.scale))
        text_at(self.screen, self.fonts["xs"], "FILTER: %s   (F / click)" % f,
                (b.x, b.y), AMBER_DIM, glow=False)
        y = b.y + int(22 * self.L.scale)
        entries = [e for e in self.log if f == CAT_ALL or e.cat == f]
        line_h = int(13 * self.L.scale)
        shown = []
        for e in entries[-40:]:
            lines = wrap_text(e.text, self.fonts["xs"], b.w - 58, 4)
            shown.append((e, lines))
        total = sum(len(l) + 0.35 for _, l in shown)
        while total * line_h > b.h - 26 and shown:
            e, l = shown.pop(0)
            total -= len(l) + 0.35
        for e, lines in shown:
            text_at(self.screen, self.fonts["xs"], e.stamp, (b.x, y),
                    PHOS_FAINT, glow=False)
            top = y
            for i, ln in enumerate(lines):
                text_at(self.screen, self.fonts["xs"], ln,
                        (b.x + 54, y + i * line_h), e.color, glow=False)
            y += line_h * len(lines) + int(5 * self.L.scale)
            if e.oid is not None:
                self.log_rects.append((pygame.Rect(b.x, top, b.w, y - top), e.oid))
        if self.interference and self.noticing_stage == 2 \
                and self.post_noticing_interf == 1:
            self.render_log_corruption(b)

    def render_log_corruption(self, b):
        if not self.interference:
            return
        if self.noticing_stage != 2:
            return
        if self.post_noticing_interf != 1:
            return

        s = pygame.Surface((b.w, b.h), pygame.SRCALPHA)
        s.fill((20, 0, 0, 210))
        self.screen.blit(s, (b.x, b.y))

        font = self.fonts["xs"]
        cw, ch = font.size("M")
        cols = max(1, b.w // max(1, cw))
        rows = max(1, b.h // max(1, ch))
        glyphs = "!@#$%^&*()_+-=[]{}|;:,.<>?/\\~`01ABCDEF"
        for _ in range(180):
            i = random.randint(0, cols - 1)
            j = random.randint(0, rows - 1)
            ch_ = random.choice(glyphs)
            x = b.x + i * cw
            y = b.y + j * ch
            col = (255, 40, 40) if random.random() < 0.7 else (140, 20, 20)
            r = font.render(ch_, True, col)
            r.set_alpha(random.randint(120, 240))
            self.screen.blit(r, (x, y))

    def render_tab_data(self, b):
        L = self.L
        y = b.y
        named = [o for o in self.world.objects if not o.proc]
        done = [o for o in named if o.stage >= 2]
        anoms = [o for o in self.world.objects if o.kind == "anomaly"]
        rows = [
            ("catalogue coverage", "%d / %d named objects" % (len(done), len(named))),
            ("field objects logged", "%d" % (self.stats["stars"] + self.stats["deep"])),
            ("anomalies classified", "%d" % self.stats["anom"]),
            ("anomalies resolved", "%d" % self.stats["resolved"]),
            ("contacts in sky", "%d" % len(anoms)),
            ("carrier recoveries", "%d" % self.stats["fixes"]),
            ("objects on screen", "%d" % getattr(self, "visible_count", 0)),
            ("survey seed", "%d" % self.seed),
        ]
        for k, v in rows:
            text_at(self.screen, self.fonts["xs"], k, (b.x, y), PHOS_DIM, glow=False)
            text_at(self.screen, self.fonts["xs"], v, (b.right, y), PHOS,
                    align="right", glow=False)
            y += int(14 * L.scale)
        y += int(8 * L.scale)
        text_at(self.screen, self.fonts["xs"],
                "RECENT ENTRIES  (click to recentre)",
                (b.x, y), AMBER_DIM, glow=False)
        y += int(16 * L.scale)
        recent = [o for o in self.world.objects if o.stage >= 1][-40:]
        for o in reversed(recent):
            if y > b.bottom - 14:
                break
            col = AMBER if o.kind == "anomaly" else (PHOS if o.kind == "star" else CYAN)
            label = o.name if len(o.name) < 30 else o.name[:29] + "."
            text_at(self.screen, self.fonts["xs"], label, (b.x, y), col, glow=False)
            text_at(self.screen, self.fonts["xs"], o.distance_text(), (b.right, y),
                    PHOS_DIM, align="right", glow=False)
            self.log_rects.append((pygame.Rect(b.x, y, b.w, int(13 * L.scale)), o.oid))
            y += int(13 * L.scale)

    def render_tab_calib(self, b):
        L = self.L
        if not self.interference and not self.calib:
            text_at(self.screen, self.fonts["sm"], "ALL CHANNELS NOMINAL",
                    (b.x, b.y), PHOS)
            y = b.y + int(26 * L.scale)
            rows = [("carrier", "LOCKED"), ("preamp", "4.2 K"),
                    ("solar glare", "%d%%" % int(getattr(self, "sol_noise", 0) * 100)),
                    ("dish servo", "TRACKING"), ("band", self.mode),
                    ("tool", self.tool or "none"),
                    ("recoveries", str(self.stats["fixes"]))]
            for k, v in rows:
                text_at(self.screen, self.fonts["xs"], k, (b.x, y), PHOS_DIM, glow=False)
                text_at(self.screen, self.fonts["xs"], v, (b.right, y), PHOS,
                        align="right", glow=False)
                y += int(14 * L.scale)
            y += int(10 * L.scale)
            for ln in wrap_text("If broadband interference hits, this panel is where "
                                "you re-phase the three receiver channels. Nothing else "
                                "works until the carrier is back.",
                                self.fonts["xs"], b.w):
                text_at(self.screen, self.fonts["xs"], ln, (b.x, y),
                        PHOS_FAINT, glow=False)
                y += int(13 * L.scale)
            self.calib_rects = []
            return

        if self.calib is None:
            self.start_calibration()
        c = self.calib
        text_at(self.screen, self.fonts["sm"], "RE-PHASE RECEIVER", (b.x, b.y), RED_WARN)
        text_at(self.screen, self.fonts["xs"],
                "W/S pick channel   A/D slide   SPACE lock",
                (b.x, b.y + int(20 * L.scale)), AMBER_DIM, glow=False)
        y = b.y + int(40 * L.scale)
        self.calib_rects = []
        gh = int(46 * L.scale)
        for i, band in enumerate(c["bands"]):
            row = pygame.Rect(b.x, y, b.w, gh)
            self.calib_rects.append(row)
            sel = (i == c["sel"])
            col = PHOS if band["lock"] else (AMBER if sel else PHOS_DIM)
            pygame.draw.rect(self.screen, PHOS_FAINT, row, 1)
            for which, val, cc in ((0, band["tgt"], PHOS_FAINT), (1, band["cur"], col)):
                pts = []
                for px in range(0, row.w - 4, 3):
                    f = px / max(1, row.w - 4)
                    ph = val * 12.0
                    v = math.sin(f * (6 + band["freq"] * 3) * math.pi + ph * math.pi)
                    if which == 1 and not band["lock"]:
                        v += math.sin(f * 33 + c["t"] * 5) * 0.12
                    pts.append((row.x + 2 + px, row.centery - v * (gh * 0.30)))
                if len(pts) > 1:
                    pygame.draw.lines(self.screen, cc, False, pts, 2 if which else 1)
            err = abs(band["cur"] - band["tgt"])
            txt = "CH%d  LOCKED" % (i + 1) if band["lock"] else \
                  "CH%d  phase err %.3f%s" % (i + 1, err,
                                              "   <-- SPACE" if err < 0.035 else "")
            text_at(self.screen, self.fonts["xs"], txt, (row.x + 4, row.y + 2),
                    col, glow=sel or band["lock"])
            sy = row.bottom - int(7 * L.scale)
            pygame.draw.line(self.screen, PHOS_FAINT,
                             (row.x + 2, sy), (row.right - 2, sy), 1)
            tx = row.x + 2 + band["tgt"] * (row.w - 4)
            pygame.draw.line(self.screen, PHOS_DIM, (tx, sy - 4), (tx, sy + 4), 1)
            cxp = row.x + 2 + band["cur"] * (row.w - 4)
            pygame.draw.polygon(self.screen, col,
                                [(cxp, sy - 5), (cxp - 4, sy + 3), (cxp + 4, sy + 3)])
            y += gh + int(8 * L.scale)
        n = sum(1 for x in c["bands"] if x["lock"])
        text_at(self.screen, self.fonts["xs"], "%d / 3 channels phased" % n,
                (b.x, y + 4), PHOS if n == 3 else AMBER, glow=False)

    # ---- help tab (sub-paged, aligned columns) ----------------------------
    def render_tab_help(self, b):
        L = self.L
        pages = ["CONTROLS", "TOOLS", "SCIENCE", "ANOMALIES"]
        chip_w = b.w // len(pages)
        for i, pname in enumerate(pages):
            tr = pygame.Rect(b.x + i * chip_w, b.y, chip_w, int(18 * L.scale))
            active = (i == self.help_page)
            col = PHOS if active else PHOS_DIM
            if active:
                pygame.draw.rect(self.screen, (0, 26, 20), tr)
            pygame.draw.rect(self.screen, PHOS_FAINT, tr, 1)
            text_at(self.screen, self.fonts["xs"], pname,
                    (tr.centerx, tr.y + int(3 * L.scale)), col,
                    align="center", glow=active)
            self.help_nav_rects.append((tr, i))
        y = b.y + int(24 * L.scale)

        if self.help_page == 0:
            lines = [
                ("MOVE", "WASD / arrows  (SHIFT = fast)"),
                ("AIM", "mouse      PAN: middle-drag"),
                ("ZOOM", "wheel  /  + -"),
                ("SCAN", "hold LMB on a contact"),
                ("MODE", "1 VISUAL  2 THERMAL  3 RADIO"),
                ("TOOL", "4 5 6 7 8 9  --  X radial menu"),
                ("MAP", "0 finder chart"),
                ("REDSHIFT", "Q / E  (SHIFT coarse, Z reset)"),
                ("MONITOR", "R toggle  --  hold LMB to link"),
                ("PANEL", "TAB cycles  H hides"),
                ("FILTER", "F cycles the log filter"),
                ("SAVE", "F5 quick save  F9 quick load"),
                ("CODEX", "K opens field guide"),
                ("MENU", "ESC or M"),
            ]
            key_w = max(self.fonts["xs"].size(k)[0] for k, _ in lines) + int(14 * L.scale)
            for k, v in lines:
                text_at(self.screen, self.fonts["xs"], k, (b.x, y),
                        AMBER_DIM, glow=False)
                text_at(self.screen, self.fonts["xs"], v, (b.x + key_w, y),
                        PHOS_DIM, glow=False)
                y += int(14 * L.scale)

        elif self.help_page == 1:
            text_at(self.screen, self.fonts["xs"], "TOOLS (keys 4-9, or X radial)",
                    (b.x, y), AMBER_DIM, glow=False)
            y += int(15 * L.scale)
            tools_help = [
                ("SPECTRO", "spectral lines on match"),
                ("POLARI", "polarisation, needed for exotic"),
                ("INTERF", "wider scan radius, resolves smudges"),
                ("RANGE", "adds explicit distance to log"),
                ("PHOTO", "required to solve variable dims"),
                ("CMB", "needed at high redshift"),
            ]
            tw = max(self.fonts["xs"].size(k)[0] for k, _ in tools_help) + int(14 * L.scale)
            for k, v in tools_help:
                text_at(self.screen, self.fonts["xs"], k, (b.x, y),
                        AMBER_DIM, glow=False)
                text_at(self.screen, self.fonts["xs"], v, (b.x + tw, y),
                        PHOS_DIM, glow=False)
                y += int(14 * L.scale)
            y += int(8 * L.scale)
            for ln in wrap_text(
                    "Bands and tools stack. A tool changes what a scan finds; "
                    "the band decides whether the contact answers at all.",
                    self.fonts["xs"], b.w):
                text_at(self.screen, self.fonts["xs"], ln, (b.x, y),
                        PHOS_FAINT, glow=False)
                y += int(13 * L.scale)

        elif self.help_page == 2:
            paras = [
                "Contacts answer on one band. A red giant is loudest on THERMAL, "
                "a quasar on RADIO, most stars on VISUAL. Wrong band, slow scan.",
                "The dial is depth. z=0 is the local sky; turning it up trades "
                "nearby stars for the deep universe. At z=1089 there is nothing "
                "further to see.",
                "Cosmology readouts under the dial are integrated from a flat "
                "LCDM model with Planck-ish parameters. They are not decoration.",
            ]
            for para in paras:
                for ln in wrap_text(para, self.fonts["xs"], b.w):
                    text_at(self.screen, self.fonts["xs"], ln, (b.x, y),
                            PHOS_FAINT, glow=False)
                    y += int(13 * L.scale)
                y += int(6 * L.scale)

        else:
            paras = [
                "Anomalies take two passes. The first classifies the contact. "
                "After about three in-game hours, a second pass resolves it.",
                "Some belong to a chain. Resolving one link reveals a bearing "
                "-- watch the edge of the sky for a chevron.",
                "Variable stars dim on a schedule. Red rings mark a dip; switch "
                "to the PHOTO tool to solve the cycle when it happens.",
            ]
            for para in paras:
                for ln in wrap_text(para, self.fonts["xs"], b.w):
                    text_at(self.screen, self.fonts["xs"], ln, (b.x, y),
                            PHOS_FAINT, glow=False)
                    y += int(13 * L.scale)
                y += int(6 * L.scale)

    # ---- CRT --------------------------------------------------------------
    def render_crt(self):
        if not self.settings["crt"]:
            return
        L = self.L

        if self.horror_t >= 0:
            f = clamp(self.horror_t / HORROR_DURATION, 0.0, 1.0)
            for _ in range(int(1 + f * 5)):
                fr = self.static_frames[random.randint(0, len(self.static_frames) - 1)]
                self.screen.blit(fr, (random.randint(-14, 14),
                                      random.randint(-14, 14)))
            veil = pygame.Surface((L.w, L.h), pygame.SRCALPHA)
            veil.fill((0, 0, 0, int(210 * f)))
            self.screen.blit(veil, (0, 0))
            return

        if abs(self.shift) > 0.4:
            snap = self.screen.copy()
            self.screen.blit(snap, (self.shift, 0))
        if self.state == "PLAY" and self.interference:
            f = self.static_frames[int(self.fx_i * 2) % len(self.static_frames)]
            s = L.sky
            if L.panel_open:
                region = pygame.Rect(s.x, s.y, max(0, L.panel.left - s.x), s.h)
            else:
                region = s
            if region.w > 0 and region.h > 0:
                prev_clip = self.screen.get_clip()
                self.screen.set_clip(region)
                self.screen.blit(f, (random.randint(-4, 4), random.randint(-4, 4)))
                self.screen.set_clip(prev_clip)
        elif self.state == "PLAY" and getattr(self, "sol_noise", 0) > 0.05:
            f = self.static_frames[int(self.fx_i) % len(self.static_frames)]
            f.set_alpha(int(80 * self.sol_noise))
            self.screen.blit(f, (0, 0))
            f.set_alpha(255)
        self.screen.blit(self.noise_tiles[int(self.fx_i) % len(self.noise_tiles)], (0, 0))
        self.screen.blit(self.scanlines, (0, 0))
        self.screen.blit(self.vignette, (0, 0))
        if getattr(self, "glitch_flash", 0) > 0:
            s = pygame.Surface((L.w, L.h), pygame.SRCALPHA)
            s.fill((PHOS[0], PHOS[1], PHOS[2],
                    int(28 * clamp(self.glitch_flash / 0.16, 0, 1))))
            self.screen.blit(s, (0, 0))

    # ================================================================== MENU
    def button(self, rect, label, sub="", active=False, danger=False):
        col = RED_WARN if danger else (AMBER if active else PHOS)
        hover = rect.collidepoint(pygame.mouse.get_pos())
        panel_rect(self.screen, rect,
                   border=col if (hover or active) else PHOS_FAINT,
                   fill=(0, 30, 22, 190) if hover else (0, 14, 11, 150))
        text_at(self.screen, self.fonts["md"], label,
                (rect.x + int(16 * self.L.scale), rect.y + int(8 * self.L.scale)),
                col, glow=hover or active)
        if sub:
            text_at(self.screen, self.fonts["xs"], sub,
                    (rect.right - int(14 * self.L.scale),
                     rect.y + int(13 * self.L.scale)),
                    PHOS_DIM, align="right", glow=False)
        return rect

    def render_menu(self):
        L = self.L
        t = self.menu_t
        for (fx, fy, br, ph) in self.menu_stars:
            x = int((fx * L.w + t * 5 * br) % L.w)
            y = int(fy * L.h)
            b = int(40 + 120 * br * (0.6 + 0.4 * math.sin(t * 1.4 + ph)))
            self.screen.set_at((x, y), (int(b * 0.7), b, int(b * 0.85)))

        cx = int(L.w * 0.5)
        text_at(self.screen, self.fonts["title"], "VYSTLZ",
                (cx, int(L.h * 0.10)), PHOS, align="center")
        text_at(self.screen, self.fonts["title"], "DEEP SKY",
                (cx, int(L.h * 0.10 + 52 * L.scale)), AMBER, align="center")
        text_at(self.screen, self.fonts["xs"],
                "ground array  //  observation only  //  v%s" % VERSION,
                (cx, int(L.h * 0.10 + 112 * L.scale)),
                PHOS_DIM, align="center", glow=False)

        self.buttons = []
        bw, bh = int(clamp(L.w * 0.34, 300, 460)), int(40 * L.scale)
        x = cx - bw // 2
        y = int(L.h * 0.40)
        gap = int(bh + 10 * L.scale)

        if self.menu_page == "MAIN":
            has_save = any(self.save_meta(i) for i in range(1, SAVE_SLOTS + 1))
            items = [("new", "NEW SURVEY", "fresh seed"),
                     ("continue", "CONTINUE",
                      "most recent save" if has_save else "no saves"),
                     ("load", "LOAD SURVEY", ""),
                     ("settings", "SETTINGS", ""),
                     ("about", "ABOUT", ""),
                     ("quit", "QUIT", "esc")]
            for key, lab, sub in items:
                r = pygame.Rect(x, y, bw, bh)
                self.buttons.append((self.button(r, lab, sub), key))
                y += gap
        elif self.menu_page == "LOAD":
            text_at(self.screen, self.fonts["md"], "SELECT SLOT",
                    (cx, y - int(34 * L.scale)), PHOS, align="center")
            for i in range(1, SAVE_SLOTS + 1):
                m = self.save_meta(i)
                sub = "empty" if not m else "%s   D%02d   %d pts" % (
                    m["saved"], int(m["hours"] // 24) + 1, m["score"])
                r = pygame.Rect(x, y, bw, bh)
                self.buttons.append((self.button(r, "SLOT %d" % i, sub), "load%d" % i))
                y += gap
            self.buttons.append((self.button(pygame.Rect(x, y, bw, bh), "BACK"), "back"))
        elif self.menu_page == "SETTINGS":
            for key, lab in (("crt", "CRT FILTER"), ("audio", "AUDIO"),
                             ("hints", "HINT LINE")):
                r = pygame.Rect(x, y, bw, bh)
                self.buttons.append((self.button(r, lab,
                                                 "ON" if self.settings[key] else "OFF",
                                                 active=self.settings[key]),
                                     "set_" + key))
                y += gap
            self.buttons.append((self.button(pygame.Rect(x, y, bw, bh),
                                             "FULLSCREEN (F11)",
                                             "on" if self.fullscreen else "off"),
                                 "fullscreen"))
            y += gap
            self.buttons.append((self.button(pygame.Rect(x, y, bw, bh), "BACK"), "back"))
        elif self.menu_page == "ABOUT":
            txt = ("You run a ground receiver array. There is no ship, no fuel, "
                   "no oxygen and nothing out here can reach you. You point the "
                   "dish, pick a band, tune the redshift, and write down what "
                   "answers.\n\n"
                   "The catalogue is real: star positions, deep sky objects, "
                   "redshifts and distances are the published figures, and the "
                   "cosmology readouts are integrated from a flat LCDM model. "
                   "The anomalies are not real. Probably.\n\n"
                   "Made for someone with no cosmology degree and no patience "
                   "for clutter.")
            yy = int(L.h * 0.34)
            for para in txt.split("\n"):
                for ln in wrap_text(para, self.fonts["sm"], int(L.w * 0.6)):
                    text_at(self.screen, self.fonts["sm"], ln, (cx, yy),
                            PHOS_DIM, align="center", glow=False)
                    yy += int(19 * L.scale)
            self.buttons.append((self.button(
                pygame.Rect(x, int(L.h * 0.80), bw, bh), "BACK"), "back"))

        if self.menu_msg_t > 0:
            text_at(self.screen, self.fonts["sm"], self.menu_msg,
                    (cx, L.h - int(40 * L.scale)), RED_WARN, align="center")

    def menu_click(self, e):
        if e.button != 1:
            return
        for rect, key in self.buttons:
            if not rect.collidepoint(e.pos):
                continue
            self.audio.play(self.audio.s_ui, 0.6)
            if key == "new":
                self.new_session()
            elif key == "continue":
                best, best_m = None, None
                for i in range(1, SAVE_SLOTS + 1):
                    m = self.save_meta(i)
                    if m and (best_m is None or m["saved"] > best_m["saved"]):
                        best, best_m = i, m
                if best:
                    self.load_game(best)
                else:
                    self.menu_msg = "NO SAVED SURVEYS"
                    self.menu_msg_t = 2.5
            elif key == "load":
                self.menu_page = "LOAD"
            elif key == "settings":
                self.menu_page = "SETTINGS"
            elif key == "about":
                self.menu_page = "ABOUT"
            elif key == "quit":
                self.running = False
            elif key == "back":
                self.menu_page = "MAIN"
            elif key == "fullscreen":
                self.toggle_fullscreen()
            elif key.startswith("set_"):
                k = key[4:]
                self.settings[k] = not self.settings[k]
                if k == "audio":
                    self.audio.enabled = self.settings["audio"]
                    if not self.audio.enabled:
                        self.audio.set_hum_pan(0.5, 0)
                        self.audio.set_static(0)
            elif key.startswith("load"):
                slot = int(key[4:])
                if not self.load_game(slot):
                    self.menu_msg = "SLOT %d IS EMPTY" % slot
                    self.menu_msg_t = 2.5
            return

    # ================================================================= PAUSE
    def render_pause(self):
        L = self.L
        veil = pygame.Surface((L.w, L.h), pygame.SRCALPHA)
        veil.fill((0, 6, 5, 190))
        self.screen.blit(veil, (0, 0))
        cx = L.w // 2
        page = getattr(self, "pause_page", "MAIN")
        text_at(self.screen, self.fonts["xl"], "ARRAY PAUSED",
                (cx, int(L.h * 0.16)), PHOS, align="center")
        text_at(self.screen, self.fonts["xs"],
                "%s    score %06d    seed %d" % (self.clock_str(), self.score, self.seed),
                (cx, int(L.h * 0.16 + 44 * L.scale)),
                PHOS_DIM, align="center", glow=False)

        self.buttons = []
        bw, bh = int(clamp(L.w * 0.32, 290, 430)), int(38 * L.scale)
        x, y = cx - bw // 2, int(L.h * 0.30)
        gap = int(bh + 9 * L.scale)

        if page == "MAIN":
            items = [("resume", "RESUME", "esc"), ("save", "SAVE SURVEY", "F5 quick"),
                     ("load", "LOAD SURVEY", "F9 quick"), ("settings", "SETTINGS", ""),
                     ("menu", "MAIN MENU", "unsaved progress lost"),
                     ("quit", "QUIT", "")]
            for key, lab, sub in items:
                self.buttons.append((self.button(pygame.Rect(x, y, bw, bh), lab, sub,
                                                 danger=(key in ("menu", "quit"))),
                                     "p_" + key))
                y += gap
        elif page in ("SAVE", "LOAD"):
            text_at(self.screen, self.fonts["md"], page + " SLOT",
                    (cx, y - int(30 * L.scale)), AMBER, align="center")
            for i in range(1, SAVE_SLOTS + 1):
                m = self.save_meta(i)
                sub = "empty" if not m else "%s  D%02d  %d pts" % (
                    m["saved"], int(m["hours"] // 24) + 1, m["score"])
                self.buttons.append((self.button(pygame.Rect(x, y, bw, bh),
                                                 "SLOT %d" % i, sub),
                                     "%s%d" % (page.lower(), i)))
                y += gap
            self.buttons.append((self.button(pygame.Rect(x, y, bw, bh), "BACK"), "p_back"))
        elif page == "SETTINGS":
            for key, lab in (("crt", "CRT FILTER"), ("audio", "AUDIO"),
                             ("hints", "HINT LINE")):
                self.buttons.append((self.button(pygame.Rect(x, y, bw, bh), lab,
                                                 "ON" if self.settings[key] else "OFF",
                                                 active=self.settings[key]),
                                     "pset_" + key))
                y += gap
            self.buttons.append((self.button(pygame.Rect(x, y, bw, bh),
                                             "FULLSCREEN (F11)",
                                             "on" if self.fullscreen else "off"),
                                 "p_fullscreen"))
            y += gap
            self.buttons.append((self.button(pygame.Rect(x, y, bw, bh), "BACK"), "p_back"))

        if self.toast_t > 0:
            text_at(self.screen, self.fonts["sm"], self.toast,
                    (cx, L.h - int(46 * L.scale)), AMBER, align="center")

    def pause_click(self, e):
        if e.button != 1:
            return
        for rect, key in self.buttons:
            if not rect.collidepoint(e.pos):
                continue
            self.audio.play(self.audio.s_ui, 0.6)
            if key == "p_resume":
                self.state = "PLAY"
            elif key == "p_save":
                self.pause_page = "SAVE"
            elif key == "p_load":
                self.pause_page = "LOAD"
            elif key == "p_settings":
                self.pause_page = "SETTINGS"
            elif key == "p_back":
                self.pause_page = "MAIN"
            elif key == "p_menu":
                self.state = "MENU"
                self.menu_page = "MAIN"
            elif key == "p_quit":
                self.running = False
            elif key == "p_fullscreen":
                self.toggle_fullscreen()
            elif key.startswith("pset_"):
                k = key[5:]
                self.settings[k] = not self.settings[k]
                if k == "audio":
                    self.audio.enabled = self.settings["audio"]
                    if not self.audio.enabled:
                        self.audio.set_hum_pan(0.5, 0)
                        self.audio.set_static(0)
            elif key.startswith("save"):
                self.save_game(int(key[4:]))
                self.pause_page = "MAIN"
            elif key.startswith("load"):
                slot = int(key[4:])
                if self.load_game(slot):
                    self.state = "PLAY"
                else:
                    self.toast = "SLOT %d IS EMPTY" % slot
                    self.toast_t = 2.5
            return


# ==========================================================================
def _enable_dpi_awareness():
    """On Windows, tell the OS we handle DPI ourselves."""
    if sys.platform != "win32":
        return
    try:
        import ctypes
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
            return
        except Exception:
            pass
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass
    except Exception:
        pass


def main():
    _enable_dpi_awareness()
    try:
        Game().run()
    except KeyboardInterrupt:
        pygame.quit()


if __name__ == "__main__":
    main()