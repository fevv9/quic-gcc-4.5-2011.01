;; ##################################################################
;; # Copyright (c) $Date$ Qualcomm Innovation Center, Inc..
;; # All Rights Reserved.
;; # Modified by Qualcomm Innovation Center, Inc. on $Date$
;; ##################################################################
(define_constants [
  (UNSPEC_QDSP6_Q6C2_cmpeq 1000)
  (UNSPEC_QDSP6_Q6C2_cmpgt 1001)
  (UNSPEC_QDSP6_Q6C2_cmpgtu 1002)
  (UNSPEC_QDSP6_Q6C2_cmpeqp 1003)
  (UNSPEC_QDSP6_Q6C2_cmpgtp 1004)
  (UNSPEC_QDSP6_Q6C2_cmpgtup 1005)
  (UNSPEC_QDSP6_Q6A4_rcmpeqi 1006)
  (UNSPEC_QDSP6_Q6A4_rcmpneqi 1007)
  (UNSPEC_QDSP6_Q6A4_rcmpeq 1008)
  (UNSPEC_QDSP6_Q6A4_rcmpneq 1009)
  (UNSPEC_QDSP6_Q6C2_bitsset 1010)
  (UNSPEC_QDSP6_Q6C2_bitsclr 1011)
  (UNSPEC_QDSP6_Q6C4_nbitsset 1012)
  (UNSPEC_QDSP6_Q6C4_nbitsclr 1013)
  (UNSPEC_QDSP6_Q6C2_cmpeqi 1014)
  (UNSPEC_QDSP6_Q6C2_cmpgti 1015)
  (UNSPEC_QDSP6_Q6C2_cmpgtui 1016)
  (UNSPEC_QDSP6_Q6C2_cmpgei 1017)
  (UNSPEC_QDSP6_Q6C2_cmpgeui 1018)
  (UNSPEC_QDSP6_Q6C2_cmplt 1019)
  (UNSPEC_QDSP6_Q6C2_cmpltu 1020)
  (UNSPEC_QDSP6_Q6C2_bitsclri 1021)
  (UNSPEC_QDSP6_Q6C4_nbitsclri 1022)
  (UNSPEC_QDSP6_Q6C4_cmpneqi 1023)
  (UNSPEC_QDSP6_Q6C4_cmpltei 1024)
  (UNSPEC_QDSP6_Q6C4_cmplteui 1025)
  (UNSPEC_QDSP6_Q6C4_cmpneq 1026)
  (UNSPEC_QDSP6_Q6C4_cmplte 1027)
  (UNSPEC_QDSP6_Q6C4_cmplteu 1028)
  (UNSPEC_QDSP6_Q6C2_and 1029)
  (UNSPEC_QDSP6_Q6C2_or 1030)
  (UNSPEC_QDSP6_Q6C2_xor 1031)
  (UNSPEC_QDSP6_Q6C2_andn 1032)
  (UNSPEC_QDSP6_Q6C2_not 1033)
  (UNSPEC_QDSP6_Q6C2_orn 1034)
  (UNSPEC_QDSP6_Q6C4_and_and 1035)
  (UNSPEC_QDSP6_Q6C4_and_or 1036)
  (UNSPEC_QDSP6_Q6C4_or_and 1037)
  (UNSPEC_QDSP6_Q6C4_or_or 1038)
  (UNSPEC_QDSP6_Q6C4_and_andn 1039)
  (UNSPEC_QDSP6_Q6C4_and_orn 1040)
  (UNSPEC_QDSP6_Q6C4_or_andn 1041)
  (UNSPEC_QDSP6_Q6C4_or_orn 1042)
  (UNSPEC_QDSP6_Q6C2_pxfer_map 1043)
  (UNSPEC_QDSP6_Q6C2_any8 1044)
  (UNSPEC_QDSP6_Q6C2_all8 1045)
  (UNSPEC_QDSP6_Q6C2_vitpack 1046)
  (UNSPEC_QDSP6_Q6C2_mux 1047)
  (UNSPEC_QDSP6_Q6C2_muxii 1048)
  (UNSPEC_QDSP6_Q6C2_muxir 1049)
  (UNSPEC_QDSP6_Q6C2_muxri 1050)
  (UNSPEC_QDSP6_Q6C2_vmux 1051)
  (UNSPEC_QDSP6_Q6C2_mask 1052)
  (UNSPEC_QDSP6_Q6A2_vcmpbeq 1053)
  (UNSPEC_QDSP6_Q6A4_vcmpbeqi 1054)
  (UNSPEC_QDSP6_Q6A4_vcmpbeq_any 1055)
  (UNSPEC_QDSP6_Q6A2_vcmpbgtu 1056)
  (UNSPEC_QDSP6_Q6A4_vcmpbgtui 1057)
  (UNSPEC_QDSP6_Q6A4_vcmpbgt 1058)
  (UNSPEC_QDSP6_Q6A4_vcmpbgti 1059)
  (UNSPEC_QDSP6_Q6A4_cmpbeq 1060)
  (UNSPEC_QDSP6_Q6A4_cmpbeqi 1061)
  (UNSPEC_QDSP6_Q6A4_cmpbgtu 1062)
  (UNSPEC_QDSP6_Q6A4_cmpbgtui 1063)
  (UNSPEC_QDSP6_Q6A4_cmpbgt 1064)
  (UNSPEC_QDSP6_Q6A4_cmpbgti 1065)
  (UNSPEC_QDSP6_Q6A2_vcmpheq 1066)
  (UNSPEC_QDSP6_Q6A2_vcmphgt 1067)
  (UNSPEC_QDSP6_Q6A2_vcmphgtu 1068)
  (UNSPEC_QDSP6_Q6A4_vcmpheqi 1069)
  (UNSPEC_QDSP6_Q6A4_vcmphgti 1070)
  (UNSPEC_QDSP6_Q6A4_vcmphgtui 1071)
  (UNSPEC_QDSP6_Q6A4_cmpheq 1072)
  (UNSPEC_QDSP6_Q6A4_cmphgt 1073)
  (UNSPEC_QDSP6_Q6A4_cmphgtu 1074)
  (UNSPEC_QDSP6_Q6A4_cmpheqi 1075)
  (UNSPEC_QDSP6_Q6A4_cmphgti 1076)
  (UNSPEC_QDSP6_Q6A4_cmphgtui 1077)
  (UNSPEC_QDSP6_Q6A2_vcmpweq 1078)
  (UNSPEC_QDSP6_Q6A2_vcmpwgt 1079)
  (UNSPEC_QDSP6_Q6A2_vcmpwgtu 1080)
  (UNSPEC_QDSP6_Q6A4_vcmpweqi 1081)
  (UNSPEC_QDSP6_Q6A4_vcmpwgti 1082)
  (UNSPEC_QDSP6_Q6A4_vcmpwgtui 1083)
  (UNSPEC_QDSP6_Q6A4_boundscheck 1084)
  (UNSPEC_QDSP6_Q6A4_tlbmatch 1085)
  (UNSPEC_QDSP6_Q6C2_tfrpr 1086)
  (UNSPEC_QDSP6_Q6C2_tfrrp 1087)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_hh_s0 1088)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_hh_s1 1089)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_hl_s0 1090)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_hl_s1 1091)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_lh_s0 1092)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_lh_s1 1093)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_ll_s0 1094)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_ll_s1 1095)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_hh_s0 1096)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_hh_s1 1097)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_hl_s0 1098)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_hl_s1 1099)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_lh_s0 1100)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_lh_s1 1101)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_ll_s0 1102)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_ll_s1 1103)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hh_s0 1104)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hh_s1 1105)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hl_s0 1106)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hl_s1 1107)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_lh_s0 1108)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_lh_s1 1109)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_ll_s0 1110)
  (UNSPEC_QDSP6_Q6M2_mpy_acc_sat_ll_s1 1111)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hh_s0 1112)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hh_s1 1113)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hl_s0 1114)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hl_s1 1115)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_lh_s0 1116)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_lh_s1 1117)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_ll_s0 1118)
  (UNSPEC_QDSP6_Q6M2_mpy_nac_sat_ll_s1 1119)
  (UNSPEC_QDSP6_Q6M2_mpy_hh_s0 1120)
  (UNSPEC_QDSP6_Q6M2_mpy_hh_s1 1121)
  (UNSPEC_QDSP6_Q6M2_mpy_hl_s0 1122)
  (UNSPEC_QDSP6_Q6M2_mpy_hl_s1 1123)
  (UNSPEC_QDSP6_Q6M2_mpy_lh_s0 1124)
  (UNSPEC_QDSP6_Q6M2_mpy_lh_s1 1125)
  (UNSPEC_QDSP6_Q6M2_mpy_ll_s0 1126)
  (UNSPEC_QDSP6_Q6M2_mpy_ll_s1 1127)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_hh_s0 1128)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_hh_s1 1129)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_hl_s0 1130)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_hl_s1 1131)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_lh_s0 1132)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_lh_s1 1133)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_ll_s0 1134)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_ll_s1 1135)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_hh_s0 1136)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_hh_s1 1137)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_hl_s0 1138)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_hl_s1 1139)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_lh_s0 1140)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_lh_s1 1141)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_ll_s0 1142)
  (UNSPEC_QDSP6_Q6M2_mpy_rnd_ll_s1 1143)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hh_s0 1144)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hh_s1 1145)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hl_s0 1146)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hl_s1 1147)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_lh_s0 1148)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_lh_s1 1149)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_ll_s0 1150)
  (UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_ll_s1 1151)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_hh_s0 1152)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_hh_s1 1153)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_hl_s0 1154)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_hl_s1 1155)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_lh_s0 1156)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_lh_s1 1157)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_ll_s0 1158)
  (UNSPEC_QDSP6_Q6M2_mpyd_acc_ll_s1 1159)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_hh_s0 1160)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_hh_s1 1161)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_hl_s0 1162)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_hl_s1 1163)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_lh_s0 1164)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_lh_s1 1165)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_ll_s0 1166)
  (UNSPEC_QDSP6_Q6M2_mpyd_nac_ll_s1 1167)
  (UNSPEC_QDSP6_Q6M2_mpyd_hh_s0 1168)
  (UNSPEC_QDSP6_Q6M2_mpyd_hh_s1 1169)
  (UNSPEC_QDSP6_Q6M2_mpyd_hl_s0 1170)
  (UNSPEC_QDSP6_Q6M2_mpyd_hl_s1 1171)
  (UNSPEC_QDSP6_Q6M2_mpyd_lh_s0 1172)
  (UNSPEC_QDSP6_Q6M2_mpyd_lh_s1 1173)
  (UNSPEC_QDSP6_Q6M2_mpyd_ll_s0 1174)
  (UNSPEC_QDSP6_Q6M2_mpyd_ll_s1 1175)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_hh_s0 1176)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_hh_s1 1177)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_hl_s0 1178)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_hl_s1 1179)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_lh_s0 1180)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_lh_s1 1181)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_ll_s0 1182)
  (UNSPEC_QDSP6_Q6M2_mpyd_rnd_ll_s1 1183)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_hh_s0 1184)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_hh_s1 1185)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_hl_s0 1186)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_hl_s1 1187)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_lh_s0 1188)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_lh_s1 1189)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_ll_s0 1190)
  (UNSPEC_QDSP6_Q6M2_mpyu_acc_ll_s1 1191)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_hh_s0 1192)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_hh_s1 1193)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_hl_s0 1194)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_hl_s1 1195)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_lh_s0 1196)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_lh_s1 1197)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_ll_s0 1198)
  (UNSPEC_QDSP6_Q6M2_mpyu_nac_ll_s1 1199)
  (UNSPEC_QDSP6_Q6M2_mpyu_hh_s0 1200)
  (UNSPEC_QDSP6_Q6M2_mpyu_hh_s1 1201)
  (UNSPEC_QDSP6_Q6M2_mpyu_hl_s0 1202)
  (UNSPEC_QDSP6_Q6M2_mpyu_hl_s1 1203)
  (UNSPEC_QDSP6_Q6M2_mpyu_lh_s0 1204)
  (UNSPEC_QDSP6_Q6M2_mpyu_lh_s1 1205)
  (UNSPEC_QDSP6_Q6M2_mpyu_ll_s0 1206)
  (UNSPEC_QDSP6_Q6M2_mpyu_ll_s1 1207)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_hh_s0 1208)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_hh_s1 1209)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_hl_s0 1210)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_hl_s1 1211)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_lh_s0 1212)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_lh_s1 1213)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_ll_s0 1214)
  (UNSPEC_QDSP6_Q6M2_mpyud_acc_ll_s1 1215)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_hh_s0 1216)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_hh_s1 1217)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_hl_s0 1218)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_hl_s1 1219)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_lh_s0 1220)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_lh_s1 1221)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_ll_s0 1222)
  (UNSPEC_QDSP6_Q6M2_mpyud_nac_ll_s1 1223)
  (UNSPEC_QDSP6_Q6M2_mpyud_hh_s0 1224)
  (UNSPEC_QDSP6_Q6M2_mpyud_hh_s1 1225)
  (UNSPEC_QDSP6_Q6M2_mpyud_hl_s0 1226)
  (UNSPEC_QDSP6_Q6M2_mpyud_hl_s1 1227)
  (UNSPEC_QDSP6_Q6M2_mpyud_lh_s0 1228)
  (UNSPEC_QDSP6_Q6M2_mpyud_lh_s1 1229)
  (UNSPEC_QDSP6_Q6M2_mpyud_ll_s0 1230)
  (UNSPEC_QDSP6_Q6M2_mpyud_ll_s1 1231)
  (UNSPEC_QDSP6_Q6M2_mpysmi 1232)
  (UNSPEC_QDSP6_Q6M2_macsip 1233)
  (UNSPEC_QDSP6_Q6M2_macsin 1234)
  (UNSPEC_QDSP6_Q6M2_dpmpyss_s0 1235)
  (UNSPEC_QDSP6_Q6M2_dpmpyss_acc_s0 1236)
  (UNSPEC_QDSP6_Q6M2_dpmpyss_nac_s0 1237)
  (UNSPEC_QDSP6_Q6M2_dpmpyuu_s0 1238)
  (UNSPEC_QDSP6_Q6M2_dpmpyuu_acc_s0 1239)
  (UNSPEC_QDSP6_Q6M2_dpmpyuu_nac_s0 1240)
  (UNSPEC_QDSP6_Q6M2_mpy_up 1241)
  (UNSPEC_QDSP6_Q6M2_mpy_up_s1 1242)
  (UNSPEC_QDSP6_Q6M2_mpy_up_s1_sat 1243)
  (UNSPEC_QDSP6_Q6M2_mpyu_up 1244)
  (UNSPEC_QDSP6_Q6M2_mpysu_up 1245)
  (UNSPEC_QDSP6_Q6M2_dpmpyss_rnd_s0 1246)
  (UNSPEC_QDSP6_Q6M4_mac_up_s1_sat 1247)
  (UNSPEC_QDSP6_Q6M4_nac_up_s1_sat 1248)
  (UNSPEC_QDSP6_Q6M2_mpyi 1249)
  (UNSPEC_QDSP6_Q6M2_mpyui 1250)
  (UNSPEC_QDSP6_Q6M2_maci 1251)
  (UNSPEC_QDSP6_Q6M2_acci 1252)
  (UNSPEC_QDSP6_Q6M2_accii 1253)
  (UNSPEC_QDSP6_Q6M2_nacci 1254)
  (UNSPEC_QDSP6_Q6M2_naccii 1255)
  (UNSPEC_QDSP6_Q6M2_subacc 1256)
  (UNSPEC_QDSP6_Q6M4_mpyrr_addr 1257)
  (UNSPEC_QDSP6_Q6M4_mpyri_addr_u2 1258)
  (UNSPEC_QDSP6_Q6M4_mpyri_addr 1259)
  (UNSPEC_QDSP6_Q6M4_mpyri_addi 1260)
  (UNSPEC_QDSP6_Q6M4_mpyrr_addi 1261)
  (UNSPEC_QDSP6_Q6M2_vmpy2s_s0 1262)
  (UNSPEC_QDSP6_Q6M2_vmpy2s_s1 1263)
  (UNSPEC_QDSP6_Q6M2_vmac2s_s0 1264)
  (UNSPEC_QDSP6_Q6M2_vmac2s_s1 1265)
  (UNSPEC_QDSP6_Q6M2_vmpy2su_s0 1266)
  (UNSPEC_QDSP6_Q6M2_vmpy2su_s1 1267)
  (UNSPEC_QDSP6_Q6M2_vmac2su_s0 1268)
  (UNSPEC_QDSP6_Q6M2_vmac2su_s1 1269)
  (UNSPEC_QDSP6_Q6M2_vmpy2s_s0pack 1270)
  (UNSPEC_QDSP6_Q6M2_vmpy2s_s1pack 1271)
  (UNSPEC_QDSP6_Q6M2_vmac2 1272)
  (UNSPEC_QDSP6_Q6M2_vmpy2es_s0 1273)
  (UNSPEC_QDSP6_Q6M2_vmpy2es_s1 1274)
  (UNSPEC_QDSP6_Q6M2_vmac2es_s0 1275)
  (UNSPEC_QDSP6_Q6M2_vmac2es_s1 1276)
  (UNSPEC_QDSP6_Q6M2_vmac2es 1277)
  (UNSPEC_QDSP6_Q6M2_vrmac_s0 1278)
  (UNSPEC_QDSP6_Q6M2_vrmpy_s0 1279)
  (UNSPEC_QDSP6_Q6M2_vdmpyrs_s0 1280)
  (UNSPEC_QDSP6_Q6M2_vdmpyrs_s1 1281)
  (UNSPEC_QDSP6_Q6M2_vdmacs_s0 1282)
  (UNSPEC_QDSP6_Q6M2_vdmacs_s1 1283)
  (UNSPEC_QDSP6_Q6M2_vdmpys_s0 1284)
  (UNSPEC_QDSP6_Q6M2_vdmpys_s1 1285)
  (UNSPEC_QDSP6_Q6M2_cmpyrs_s0 1286)
  (UNSPEC_QDSP6_Q6M2_cmpyrs_s1 1287)
  (UNSPEC_QDSP6_Q6M2_cmpyrsc_s0 1288)
  (UNSPEC_QDSP6_Q6M2_cmpyrsc_s1 1289)
  (UNSPEC_QDSP6_Q6M2_cmacs_s0 1290)
  (UNSPEC_QDSP6_Q6M2_cmacs_s1 1291)
  (UNSPEC_QDSP6_Q6M2_cmacsc_s0 1292)
  (UNSPEC_QDSP6_Q6M2_cmacsc_s1 1293)
  (UNSPEC_QDSP6_Q6M2_cmpys_s0 1294)
  (UNSPEC_QDSP6_Q6M2_cmpys_s1 1295)
  (UNSPEC_QDSP6_Q6M2_cmpysc_s0 1296)
  (UNSPEC_QDSP6_Q6M2_cmpysc_s1 1297)
  (UNSPEC_QDSP6_Q6M2_cnacs_s0 1298)
  (UNSPEC_QDSP6_Q6M2_cnacs_s1 1299)
  (UNSPEC_QDSP6_Q6M2_cnacsc_s0 1300)
  (UNSPEC_QDSP6_Q6M2_cnacsc_s1 1301)
  (UNSPEC_QDSP6_Q6M2_vrcmpys_s1 1302)
  (UNSPEC_QDSP6_Q6M2_vrcmpys_acc_s1 1303)
  (UNSPEC_QDSP6_Q6M2_vrcmpys_s1rp 1304)
  (UNSPEC_QDSP6_Q6M2_mmacls_s0 1305)
  (UNSPEC_QDSP6_Q6M2_mmacls_s1 1306)
  (UNSPEC_QDSP6_Q6M2_mmachs_s0 1307)
  (UNSPEC_QDSP6_Q6M2_mmachs_s1 1308)
  (UNSPEC_QDSP6_Q6M2_mmpyl_s0 1309)
  (UNSPEC_QDSP6_Q6M2_mmpyl_s1 1310)
  (UNSPEC_QDSP6_Q6M2_mmpyh_s0 1311)
  (UNSPEC_QDSP6_Q6M2_mmpyh_s1 1312)
  (UNSPEC_QDSP6_Q6M2_mmacls_rs0 1313)
  (UNSPEC_QDSP6_Q6M2_mmacls_rs1 1314)
  (UNSPEC_QDSP6_Q6M2_mmachs_rs0 1315)
  (UNSPEC_QDSP6_Q6M2_mmachs_rs1 1316)
  (UNSPEC_QDSP6_Q6M2_mmpyl_rs0 1317)
  (UNSPEC_QDSP6_Q6M2_mmpyl_rs1 1318)
  (UNSPEC_QDSP6_Q6M2_mmpyh_rs0 1319)
  (UNSPEC_QDSP6_Q6M2_mmpyh_rs1 1320)
  (UNSPEC_QDSP6_Q6M4_vrmpyeh_s0 1321)
  (UNSPEC_QDSP6_Q6M4_vrmpyeh_s1 1322)
  (UNSPEC_QDSP6_Q6M4_vrmpyeh_acc_s0 1323)
  (UNSPEC_QDSP6_Q6M4_vrmpyeh_acc_s1 1324)
  (UNSPEC_QDSP6_Q6M4_vrmpyoh_s0 1325)
  (UNSPEC_QDSP6_Q6M4_vrmpyoh_s1 1326)
  (UNSPEC_QDSP6_Q6M4_vrmpyoh_acc_s0 1327)
  (UNSPEC_QDSP6_Q6M4_vrmpyoh_acc_s1 1328)
  (UNSPEC_QDSP6_Q6M2_hmmpyl_rs1 1329)
  (UNSPEC_QDSP6_Q6M2_hmmpyh_rs1 1330)
  (UNSPEC_QDSP6_Q6M2_hmmpyl_s1 1331)
  (UNSPEC_QDSP6_Q6M2_hmmpyh_s1 1332)
  (UNSPEC_QDSP6_Q6M2_mmaculs_s0 1333)
  (UNSPEC_QDSP6_Q6M2_mmaculs_s1 1334)
  (UNSPEC_QDSP6_Q6M2_mmacuhs_s0 1335)
  (UNSPEC_QDSP6_Q6M2_mmacuhs_s1 1336)
  (UNSPEC_QDSP6_Q6M2_mmpyul_s0 1337)
  (UNSPEC_QDSP6_Q6M2_mmpyul_s1 1338)
  (UNSPEC_QDSP6_Q6M2_mmpyuh_s0 1339)
  (UNSPEC_QDSP6_Q6M2_mmpyuh_s1 1340)
  (UNSPEC_QDSP6_Q6M2_mmaculs_rs0 1341)
  (UNSPEC_QDSP6_Q6M2_mmaculs_rs1 1342)
  (UNSPEC_QDSP6_Q6M2_mmacuhs_rs0 1343)
  (UNSPEC_QDSP6_Q6M2_mmacuhs_rs1 1344)
  (UNSPEC_QDSP6_Q6M2_mmpyul_rs0 1345)
  (UNSPEC_QDSP6_Q6M2_mmpyul_rs1 1346)
  (UNSPEC_QDSP6_Q6M2_mmpyuh_rs0 1347)
  (UNSPEC_QDSP6_Q6M2_mmpyuh_rs1 1348)
  (UNSPEC_QDSP6_Q6M2_vrcmaci_s0 1349)
  (UNSPEC_QDSP6_Q6M2_vrcmacr_s0 1350)
  (UNSPEC_QDSP6_Q6M2_vrcmaci_s0c 1351)
  (UNSPEC_QDSP6_Q6M2_vrcmacr_s0c 1352)
  (UNSPEC_QDSP6_Q6M2_cmaci_s0 1353)
  (UNSPEC_QDSP6_Q6M2_cmacr_s0 1354)
  (UNSPEC_QDSP6_Q6M2_vrcmpyi_s0 1355)
  (UNSPEC_QDSP6_Q6M2_vrcmpyr_s0 1356)
  (UNSPEC_QDSP6_Q6M2_vrcmpyi_s0c 1357)
  (UNSPEC_QDSP6_Q6M2_vrcmpyr_s0c 1358)
  (UNSPEC_QDSP6_Q6M2_cmpyi_s0 1359)
  (UNSPEC_QDSP6_Q6M2_cmpyr_s0 1360)
  (UNSPEC_QDSP6_Q6M4_cmpyi_wh 1361)
  (UNSPEC_QDSP6_Q6M4_cmpyr_wh 1362)
  (UNSPEC_QDSP6_Q6M2_vcmpy_s0_sat_i 1363)
  (UNSPEC_QDSP6_Q6M2_vcmpy_s0_sat_r 1364)
  (UNSPEC_QDSP6_Q6M2_vcmpy_s1_sat_i 1365)
  (UNSPEC_QDSP6_Q6M2_vcmpy_s1_sat_r 1366)
  (UNSPEC_QDSP6_Q6M2_vcmac_s0_sat_i 1367)
  (UNSPEC_QDSP6_Q6M2_vcmac_s0_sat_r 1368)
  (UNSPEC_QDSP6_Q6S2_vcrotate 1369)
  (UNSPEC_QDSP6_Q6S4_vrcrotate_acc 1370)
  (UNSPEC_QDSP6_Q6S4_vrcrotate 1371)
  (UNSPEC_QDSP6_Q6S2_vcnegh 1372)
  (UNSPEC_QDSP6_Q6S2_vrcnegh 1373)
  (UNSPEC_QDSP6_Q6M4_pmpyw 1374)
  (UNSPEC_QDSP6_Q6M4_vpmpyh 1375)
  (UNSPEC_QDSP6_Q6M4_pmpyw_acc 1376)
  (UNSPEC_QDSP6_Q6M4_vpmpyh_acc 1377)
  (UNSPEC_QDSP6_Q6A2_add 1378)
  (UNSPEC_QDSP6_Q6A2_sub 1379)
  (UNSPEC_QDSP6_Q6A2_addsat 1380)
  (UNSPEC_QDSP6_Q6A2_subsat 1381)
  (UNSPEC_QDSP6_Q6A2_addi 1382)
  (UNSPEC_QDSP6_Q6C4_addipc 1383)
  (UNSPEC_QDSP6_Q6A2_addh_l16_ll 1384)
  (UNSPEC_QDSP6_Q6A2_addh_l16_hl 1385)
  (UNSPEC_QDSP6_Q6A2_addh_l16_sat_ll 1386)
  (UNSPEC_QDSP6_Q6A2_addh_l16_sat_hl 1387)
  (UNSPEC_QDSP6_Q6A2_subh_l16_ll 1388)
  (UNSPEC_QDSP6_Q6A2_subh_l16_hl 1389)
  (UNSPEC_QDSP6_Q6A2_subh_l16_sat_ll 1390)
  (UNSPEC_QDSP6_Q6A2_subh_l16_sat_hl 1391)
  (UNSPEC_QDSP6_Q6A2_addh_h16_ll 1392)
  (UNSPEC_QDSP6_Q6A2_addh_h16_lh 1393)
  (UNSPEC_QDSP6_Q6A2_addh_h16_hl 1394)
  (UNSPEC_QDSP6_Q6A2_addh_h16_hh 1395)
  (UNSPEC_QDSP6_Q6A2_addh_h16_sat_ll 1396)
  (UNSPEC_QDSP6_Q6A2_addh_h16_sat_lh 1397)
  (UNSPEC_QDSP6_Q6A2_addh_h16_sat_hl 1398)
  (UNSPEC_QDSP6_Q6A2_addh_h16_sat_hh 1399)
  (UNSPEC_QDSP6_Q6A2_subh_h16_ll 1400)
  (UNSPEC_QDSP6_Q6A2_subh_h16_lh 1401)
  (UNSPEC_QDSP6_Q6A2_subh_h16_hl 1402)
  (UNSPEC_QDSP6_Q6A2_subh_h16_hh 1403)
  (UNSPEC_QDSP6_Q6A2_subh_h16_sat_ll 1404)
  (UNSPEC_QDSP6_Q6A2_subh_h16_sat_lh 1405)
  (UNSPEC_QDSP6_Q6A2_subh_h16_sat_hl 1406)
  (UNSPEC_QDSP6_Q6A2_subh_h16_sat_hh 1407)
  (UNSPEC_QDSP6_Q6A2_aslh 1408)
  (UNSPEC_QDSP6_Q6A2_asrh 1409)
  (UNSPEC_QDSP6_Q6A2_addp 1410)
  (UNSPEC_QDSP6_Q6A2_addpsat 1411)
  (UNSPEC_QDSP6_Q6A2_addsp 1412)
  (UNSPEC_QDSP6_Q6A2_subp 1413)
  (UNSPEC_QDSP6_Q6A4_addp_c 1414)
  (UNSPEC_QDSP6_Q6A4_subp_c 1415)
  (UNSPEC_QDSP6_Q6A2_neg 1416)
  (UNSPEC_QDSP6_Q6A2_negsat 1417)
  (UNSPEC_QDSP6_Q6A2_abs 1418)
  (UNSPEC_QDSP6_Q6A2_abssat 1419)
  (UNSPEC_QDSP6_Q6A2_vconj 1420)
  (UNSPEC_QDSP6_Q6A2_negp 1421)
  (UNSPEC_QDSP6_Q6A2_absp 1422)
  (UNSPEC_QDSP6_Q6A2_max 1423)
  (UNSPEC_QDSP6_Q6A2_maxu 1424)
  (UNSPEC_QDSP6_Q6A2_min 1425)
  (UNSPEC_QDSP6_Q6A2_minu 1426)
  (UNSPEC_QDSP6_Q6A2_maxp 1427)
  (UNSPEC_QDSP6_Q6A2_maxup 1428)
  (UNSPEC_QDSP6_Q6A2_minp 1429)
  (UNSPEC_QDSP6_Q6A2_minup 1430)
  (UNSPEC_QDSP6_Q6A2_tfr 1431)
  (UNSPEC_QDSP6_Q6A2_tfrsi 1432)
  (UNSPEC_QDSP6_Q6A2_tfrp 1433)
  (UNSPEC_QDSP6_Q6A2_tfrpi 1434)
  (UNSPEC_QDSP6_Q6A2_zxtb 1435)
  (UNSPEC_QDSP6_Q6A2_sxtb 1436)
  (UNSPEC_QDSP6_Q6A2_zxth 1437)
  (UNSPEC_QDSP6_Q6A2_sxth 1438)
  (UNSPEC_QDSP6_Q6A2_combinew 1439)
  (UNSPEC_QDSP6_Q6A4_combineri 1440)
  (UNSPEC_QDSP6_Q6A4_combineir 1441)
  (UNSPEC_QDSP6_Q6A2_combineii 1442)
  (UNSPEC_QDSP6_Q6A2_combine_hh 1443)
  (UNSPEC_QDSP6_Q6A2_combine_hl 1444)
  (UNSPEC_QDSP6_Q6A2_combine_lh 1445)
  (UNSPEC_QDSP6_Q6A2_combine_ll 1446)
  (UNSPEC_QDSP6_Q6A2_tfril 1447)
  (UNSPEC_QDSP6_Q6A2_tfrih 1448)
  (UNSPEC_QDSP6_Q6A2_and 1449)
  (UNSPEC_QDSP6_Q6A2_or 1450)
  (UNSPEC_QDSP6_Q6A2_xor 1451)
  (UNSPEC_QDSP6_Q6A2_not 1452)
  (UNSPEC_QDSP6_Q6M2_xor_xacc 1453)
  (UNSPEC_QDSP6_Q6M4_xor_xacc 1454)
  (UNSPEC_QDSP6_Q6A4_andn 1455)
  (UNSPEC_QDSP6_Q6A4_orn 1456)
  (UNSPEC_QDSP6_Q6A4_andnp 1457)
  (UNSPEC_QDSP6_Q6A4_ornp 1458)
  (UNSPEC_QDSP6_Q6S4_addaddi 1459)
  (UNSPEC_QDSP6_Q6S4_subaddi 1460)
  (UNSPEC_QDSP6_Q6M4_and_and 1461)
  (UNSPEC_QDSP6_Q6M4_and_andn 1462)
  (UNSPEC_QDSP6_Q6M4_and_or 1463)
  (UNSPEC_QDSP6_Q6M4_and_xor 1464)
  (UNSPEC_QDSP6_Q6M4_or_and 1465)
  (UNSPEC_QDSP6_Q6M4_or_andn 1466)
  (UNSPEC_QDSP6_Q6M4_or_or 1467)
  (UNSPEC_QDSP6_Q6M4_or_xor 1468)
  (UNSPEC_QDSP6_Q6S4_or_andix 1469)
  (UNSPEC_QDSP6_Q6S4_or_andi 1470)
  (UNSPEC_QDSP6_Q6S4_or_ori 1471)
  (UNSPEC_QDSP6_Q6M4_xor_and 1472)
  (UNSPEC_QDSP6_Q6M4_xor_or 1473)
  (UNSPEC_QDSP6_Q6M4_xor_andn 1474)
  (UNSPEC_QDSP6_Q6A2_subri 1475)
  (UNSPEC_QDSP6_Q6A2_andir 1476)
  (UNSPEC_QDSP6_Q6A2_orir 1477)
  (UNSPEC_QDSP6_Q6A2_andp 1478)
  (UNSPEC_QDSP6_Q6A2_orp 1479)
  (UNSPEC_QDSP6_Q6A2_xorp 1480)
  (UNSPEC_QDSP6_Q6A2_notp 1481)
  (UNSPEC_QDSP6_Q6A2_sxtw 1482)
  (UNSPEC_QDSP6_Q6A2_sat 1483)
  (UNSPEC_QDSP6_Q6A2_sath 1484)
  (UNSPEC_QDSP6_Q6A2_satuh 1485)
  (UNSPEC_QDSP6_Q6A2_satub 1486)
  (UNSPEC_QDSP6_Q6A2_satb 1487)
  (UNSPEC_QDSP6_Q6A2_vaddub 1488)
  (UNSPEC_QDSP6_Q6A2_vaddb_map 1489)
  (UNSPEC_QDSP6_Q6A2_vaddubs 1490)
  (UNSPEC_QDSP6_Q6A2_vaddh 1491)
  (UNSPEC_QDSP6_Q6A2_vaddhs 1492)
  (UNSPEC_QDSP6_Q6A2_vadduhs 1493)
  (UNSPEC_QDSP6_Q6A2_vaddw 1494)
  (UNSPEC_QDSP6_Q6A2_vaddws 1495)
  (UNSPEC_QDSP6_Q6S4_vxaddsubw 1496)
  (UNSPEC_QDSP6_Q6S4_vxsubaddw 1497)
  (UNSPEC_QDSP6_Q6S4_vxaddsubh 1498)
  (UNSPEC_QDSP6_Q6S4_vxsubaddh 1499)
  (UNSPEC_QDSP6_Q6S4_vxaddsubhr 1500)
  (UNSPEC_QDSP6_Q6S4_vxsubaddhr 1501)
  (UNSPEC_QDSP6_Q6A2_svavgh 1502)
  (UNSPEC_QDSP6_Q6A2_svavghs 1503)
  (UNSPEC_QDSP6_Q6A2_svnavgh 1504)
  (UNSPEC_QDSP6_Q6A2_svaddh 1505)
  (UNSPEC_QDSP6_Q6A2_svaddhs 1506)
  (UNSPEC_QDSP6_Q6A2_svadduhs 1507)
  (UNSPEC_QDSP6_Q6A2_svsubh 1508)
  (UNSPEC_QDSP6_Q6A2_svsubhs 1509)
  (UNSPEC_QDSP6_Q6A2_svsubuhs 1510)
  (UNSPEC_QDSP6_Q6A2_vraddub 1511)
  (UNSPEC_QDSP6_Q6A2_vraddub_acc 1512)
  (UNSPEC_QDSP6_Q6M2_vraddh 1513)
  (UNSPEC_QDSP6_Q6M2_vradduh 1514)
  (UNSPEC_QDSP6_Q6A2_vsubub 1515)
  (UNSPEC_QDSP6_Q6A2_vsubb_map 1516)
  (UNSPEC_QDSP6_Q6A2_vsububs 1517)
  (UNSPEC_QDSP6_Q6A2_vsubh 1518)
  (UNSPEC_QDSP6_Q6A2_vsubhs 1519)
  (UNSPEC_QDSP6_Q6A2_vsubuhs 1520)
  (UNSPEC_QDSP6_Q6A2_vsubw 1521)
  (UNSPEC_QDSP6_Q6A2_vsubws 1522)
  (UNSPEC_QDSP6_Q6A2_vabsh 1523)
  (UNSPEC_QDSP6_Q6A2_vabshsat 1524)
  (UNSPEC_QDSP6_Q6A2_vabsw 1525)
  (UNSPEC_QDSP6_Q6A2_vabswsat 1526)
  (UNSPEC_QDSP6_Q6M2_vabsdiffw 1527)
  (UNSPEC_QDSP6_Q6M2_vabsdiffh 1528)
  (UNSPEC_QDSP6_Q6A2_vrsadub 1529)
  (UNSPEC_QDSP6_Q6A2_vrsadub_acc 1530)
  (UNSPEC_QDSP6_Q6A2_vavgub 1531)
  (UNSPEC_QDSP6_Q6A2_vavguh 1532)
  (UNSPEC_QDSP6_Q6A2_vavgh 1533)
  (UNSPEC_QDSP6_Q6A2_vnavgh 1534)
  (UNSPEC_QDSP6_Q6A2_vavgw 1535)
  (UNSPEC_QDSP6_Q6A2_vnavgw 1536)
  (UNSPEC_QDSP6_Q6A2_vavgwr 1537)
  (UNSPEC_QDSP6_Q6A2_vnavgwr 1538)
  (UNSPEC_QDSP6_Q6A2_vavgwcr 1539)
  (UNSPEC_QDSP6_Q6A2_vnavgwcr 1540)
  (UNSPEC_QDSP6_Q6A2_vavghcr 1541)
  (UNSPEC_QDSP6_Q6A2_vnavghcr 1542)
  (UNSPEC_QDSP6_Q6A2_vavguw 1543)
  (UNSPEC_QDSP6_Q6A2_vavguwr 1544)
  (UNSPEC_QDSP6_Q6A2_vavgubr 1545)
  (UNSPEC_QDSP6_Q6A2_vavguhr 1546)
  (UNSPEC_QDSP6_Q6A2_vavghr 1547)
  (UNSPEC_QDSP6_Q6A2_vnavghr 1548)
  (UNSPEC_QDSP6_Q6A4_round_ri 1549)
  (UNSPEC_QDSP6_Q6A4_round_rr 1550)
  (UNSPEC_QDSP6_Q6A4_round_ri_sat 1551)
  (UNSPEC_QDSP6_Q6A4_round_rr_sat 1552)
  (UNSPEC_QDSP6_Q6A4_cround_ri 1553)
  (UNSPEC_QDSP6_Q6A4_cround_rr 1554)
  (UNSPEC_QDSP6_Q6A4_vrminh 1555)
  (UNSPEC_QDSP6_Q6A4_vrmaxh 1556)
  (UNSPEC_QDSP6_Q6A4_vrminuh 1557)
  (UNSPEC_QDSP6_Q6A4_vrmaxuh 1558)
  (UNSPEC_QDSP6_Q6A4_vrminw 1559)
  (UNSPEC_QDSP6_Q6A4_vrmaxw 1560)
  (UNSPEC_QDSP6_Q6A4_vrminuw 1561)
  (UNSPEC_QDSP6_Q6A4_vrmaxuw 1562)
  (UNSPEC_QDSP6_Q6A2_vminb 1563)
  (UNSPEC_QDSP6_Q6A2_vmaxb 1564)
  (UNSPEC_QDSP6_Q6A2_vminub 1565)
  (UNSPEC_QDSP6_Q6A2_vmaxub 1566)
  (UNSPEC_QDSP6_Q6A2_vminh 1567)
  (UNSPEC_QDSP6_Q6A2_vmaxh 1568)
  (UNSPEC_QDSP6_Q6A2_vminuh 1569)
  (UNSPEC_QDSP6_Q6A2_vmaxuh 1570)
  (UNSPEC_QDSP6_Q6A2_vminw 1571)
  (UNSPEC_QDSP6_Q6A2_vmaxw 1572)
  (UNSPEC_QDSP6_Q6A2_vminuw 1573)
  (UNSPEC_QDSP6_Q6A2_vmaxuw 1574)
  (UNSPEC_QDSP6_Q6A4_modwrapu 1575)
  (UNSPEC_QDSP6_Q6S2_asr_r_r 1576)
  (UNSPEC_QDSP6_Q6S2_asl_r_r 1577)
  (UNSPEC_QDSP6_Q6S2_lsr_r_r 1578)
  (UNSPEC_QDSP6_Q6S2_lsl_r_r 1579)
  (UNSPEC_QDSP6_Q6S2_asr_r_p 1580)
  (UNSPEC_QDSP6_Q6S2_asl_r_p 1581)
  (UNSPEC_QDSP6_Q6S2_lsr_r_p 1582)
  (UNSPEC_QDSP6_Q6S2_lsl_r_p 1583)
  (UNSPEC_QDSP6_Q6S2_asr_r_r_acc 1584)
  (UNSPEC_QDSP6_Q6S2_asl_r_r_acc 1585)
  (UNSPEC_QDSP6_Q6S2_lsr_r_r_acc 1586)
  (UNSPEC_QDSP6_Q6S2_lsl_r_r_acc 1587)
  (UNSPEC_QDSP6_Q6S2_asr_r_p_acc 1588)
  (UNSPEC_QDSP6_Q6S2_asl_r_p_acc 1589)
  (UNSPEC_QDSP6_Q6S2_lsr_r_p_acc 1590)
  (UNSPEC_QDSP6_Q6S2_lsl_r_p_acc 1591)
  (UNSPEC_QDSP6_Q6S2_asr_r_r_nac 1592)
  (UNSPEC_QDSP6_Q6S2_asl_r_r_nac 1593)
  (UNSPEC_QDSP6_Q6S2_lsr_r_r_nac 1594)
  (UNSPEC_QDSP6_Q6S2_lsl_r_r_nac 1595)
  (UNSPEC_QDSP6_Q6S2_asr_r_p_nac 1596)
  (UNSPEC_QDSP6_Q6S2_asl_r_p_nac 1597)
  (UNSPEC_QDSP6_Q6S2_lsr_r_p_nac 1598)
  (UNSPEC_QDSP6_Q6S2_lsl_r_p_nac 1599)
  (UNSPEC_QDSP6_Q6S2_asr_r_r_and 1600)
  (UNSPEC_QDSP6_Q6S2_asl_r_r_and 1601)
  (UNSPEC_QDSP6_Q6S2_lsr_r_r_and 1602)
  (UNSPEC_QDSP6_Q6S2_lsl_r_r_and 1603)
  (UNSPEC_QDSP6_Q6S2_asr_r_r_or 1604)
  (UNSPEC_QDSP6_Q6S2_asl_r_r_or 1605)
  (UNSPEC_QDSP6_Q6S2_lsr_r_r_or 1606)
  (UNSPEC_QDSP6_Q6S2_lsl_r_r_or 1607)
  (UNSPEC_QDSP6_Q6S2_asr_r_p_and 1608)
  (UNSPEC_QDSP6_Q6S2_asl_r_p_and 1609)
  (UNSPEC_QDSP6_Q6S2_lsr_r_p_and 1610)
  (UNSPEC_QDSP6_Q6S2_lsl_r_p_and 1611)
  (UNSPEC_QDSP6_Q6S2_asr_r_p_or 1612)
  (UNSPEC_QDSP6_Q6S2_asl_r_p_or 1613)
  (UNSPEC_QDSP6_Q6S2_lsr_r_p_or 1614)
  (UNSPEC_QDSP6_Q6S2_lsl_r_p_or 1615)
  (UNSPEC_QDSP6_Q6S2_asr_r_p_xor 1616)
  (UNSPEC_QDSP6_Q6S2_asl_r_p_xor 1617)
  (UNSPEC_QDSP6_Q6S2_lsr_r_p_xor 1618)
  (UNSPEC_QDSP6_Q6S2_lsl_r_p_xor 1619)
  (UNSPEC_QDSP6_Q6S2_asr_r_r_sat 1620)
  (UNSPEC_QDSP6_Q6S2_asl_r_r_sat 1621)
  (UNSPEC_QDSP6_Q6S2_asr_i_r 1622)
  (UNSPEC_QDSP6_Q6S2_lsr_i_r 1623)
  (UNSPEC_QDSP6_Q6S2_asl_i_r 1624)
  (UNSPEC_QDSP6_Q6S2_asr_i_p 1625)
  (UNSPEC_QDSP6_Q6S2_lsr_i_p 1626)
  (UNSPEC_QDSP6_Q6S2_asl_i_p 1627)
  (UNSPEC_QDSP6_Q6S2_asr_i_r_acc 1628)
  (UNSPEC_QDSP6_Q6S2_lsr_i_r_acc 1629)
  (UNSPEC_QDSP6_Q6S2_asl_i_r_acc 1630)
  (UNSPEC_QDSP6_Q6S2_asr_i_p_acc 1631)
  (UNSPEC_QDSP6_Q6S2_lsr_i_p_acc 1632)
  (UNSPEC_QDSP6_Q6S2_asl_i_p_acc 1633)
  (UNSPEC_QDSP6_Q6S2_asr_i_r_nac 1634)
  (UNSPEC_QDSP6_Q6S2_lsr_i_r_nac 1635)
  (UNSPEC_QDSP6_Q6S2_asl_i_r_nac 1636)
  (UNSPEC_QDSP6_Q6S2_asr_i_p_nac 1637)
  (UNSPEC_QDSP6_Q6S2_lsr_i_p_nac 1638)
  (UNSPEC_QDSP6_Q6S2_asl_i_p_nac 1639)
  (UNSPEC_QDSP6_Q6S2_lsr_i_r_xacc 1640)
  (UNSPEC_QDSP6_Q6S2_asl_i_r_xacc 1641)
  (UNSPEC_QDSP6_Q6S2_lsr_i_p_xacc 1642)
  (UNSPEC_QDSP6_Q6S2_asl_i_p_xacc 1643)
  (UNSPEC_QDSP6_Q6S2_asr_i_r_and 1644)
  (UNSPEC_QDSP6_Q6S2_lsr_i_r_and 1645)
  (UNSPEC_QDSP6_Q6S2_asl_i_r_and 1646)
  (UNSPEC_QDSP6_Q6S2_asr_i_r_or 1647)
  (UNSPEC_QDSP6_Q6S2_lsr_i_r_or 1648)
  (UNSPEC_QDSP6_Q6S2_asl_i_r_or 1649)
  (UNSPEC_QDSP6_Q6S2_asr_i_p_and 1650)
  (UNSPEC_QDSP6_Q6S2_lsr_i_p_and 1651)
  (UNSPEC_QDSP6_Q6S2_asl_i_p_and 1652)
  (UNSPEC_QDSP6_Q6S2_asr_i_p_or 1653)
  (UNSPEC_QDSP6_Q6S2_lsr_i_p_or 1654)
  (UNSPEC_QDSP6_Q6S2_asl_i_p_or 1655)
  (UNSPEC_QDSP6_Q6S2_asl_i_r_sat 1656)
  (UNSPEC_QDSP6_Q6S2_asr_i_r_rnd 1657)
  (UNSPEC_QDSP6_Q6S2_asr_i_r_rnd_goodsyntax 1658)
  (UNSPEC_QDSP6_Q6S4_lsli 1659)
  (UNSPEC_QDSP6_Q6S2_addasl_rrri 1660)
  (UNSPEC_QDSP6_Q6S4_andi_asl_ri 1661)
  (UNSPEC_QDSP6_Q6S4_ori_asl_ri 1662)
  (UNSPEC_QDSP6_Q6S4_addi_asl_ri 1663)
  (UNSPEC_QDSP6_Q6S4_subi_asl_ri 1664)
  (UNSPEC_QDSP6_Q6S4_andi_lsr_ri 1665)
  (UNSPEC_QDSP6_Q6S4_ori_lsr_ri 1666)
  (UNSPEC_QDSP6_Q6S4_addi_lsr_ri 1667)
  (UNSPEC_QDSP6_Q6S4_subi_lsr_ri 1668)
  (UNSPEC_QDSP6_Q6S2_valignib 1669)
  (UNSPEC_QDSP6_Q6S2_valignrb 1670)
  (UNSPEC_QDSP6_Q6S2_vspliceib 1671)
  (UNSPEC_QDSP6_Q6S2_vsplicerb 1672)
  (UNSPEC_QDSP6_Q6S2_vsplatrh 1673)
  (UNSPEC_QDSP6_Q6S2_vsplatrb 1674)
  (UNSPEC_QDSP6_Q6S2_insert 1675)
  (UNSPEC_QDSP6_Q6S2_tableidxb_goodsyntax 1676)
  (UNSPEC_QDSP6_Q6S2_tableidxh_goodsyntax 1677)
  (UNSPEC_QDSP6_Q6S2_tableidxw_goodsyntax 1678)
  (UNSPEC_QDSP6_Q6S2_tableidxd_goodsyntax 1679)
  (UNSPEC_QDSP6_Q6A4_bitspliti 1680)
  (UNSPEC_QDSP6_Q6A4_bitsplit 1681)
  (UNSPEC_QDSP6_Q6S4_extract 1682)
  (UNSPEC_QDSP6_Q6S2_extractu 1683)
  (UNSPEC_QDSP6_Q6S2_insertp 1684)
  (UNSPEC_QDSP6_Q6S4_extractp 1685)
  (UNSPEC_QDSP6_Q6S2_extractup 1686)
  (UNSPEC_QDSP6_Q6S2_insert_rp 1687)
  (UNSPEC_QDSP6_Q6S4_extract_rp 1688)
  (UNSPEC_QDSP6_Q6S2_extractu_rp 1689)
  (UNSPEC_QDSP6_Q6S2_insertp_rp 1690)
  (UNSPEC_QDSP6_Q6S4_extractp_rp 1691)
  (UNSPEC_QDSP6_Q6S2_extractup_rp 1692)
  (UNSPEC_QDSP6_Q6S2_tstbit_i 1693)
  (UNSPEC_QDSP6_Q6S4_ntstbit_i 1694)
  (UNSPEC_QDSP6_Q6S2_setbit_i 1695)
  (UNSPEC_QDSP6_Q6S2_togglebit_i 1696)
  (UNSPEC_QDSP6_Q6S2_clrbit_i 1697)
  (UNSPEC_QDSP6_Q6S2_tstbit_r 1698)
  (UNSPEC_QDSP6_Q6S4_ntstbit_r 1699)
  (UNSPEC_QDSP6_Q6S2_setbit_r 1700)
  (UNSPEC_QDSP6_Q6S2_togglebit_r 1701)
  (UNSPEC_QDSP6_Q6S2_clrbit_r 1702)
  (UNSPEC_QDSP6_Q6S2_asr_i_vh 1703)
  (UNSPEC_QDSP6_Q6S2_lsr_i_vh 1704)
  (UNSPEC_QDSP6_Q6S2_asl_i_vh 1705)
  (UNSPEC_QDSP6_Q6S2_asr_r_vh 1706)
  (UNSPEC_QDSP6_Q6S2_asl_r_vh 1707)
  (UNSPEC_QDSP6_Q6S2_lsr_r_vh 1708)
  (UNSPEC_QDSP6_Q6S2_lsl_r_vh 1709)
  (UNSPEC_QDSP6_Q6S2_asr_i_vw 1710)
  (UNSPEC_QDSP6_Q6S2_asr_i_svw_trun 1711)
  (UNSPEC_QDSP6_Q6S2_asr_r_svw_trun 1712)
  (UNSPEC_QDSP6_Q6S2_lsr_i_vw 1713)
  (UNSPEC_QDSP6_Q6S2_asl_i_vw 1714)
  (UNSPEC_QDSP6_Q6S2_asr_r_vw 1715)
  (UNSPEC_QDSP6_Q6S2_asl_r_vw 1716)
  (UNSPEC_QDSP6_Q6S2_lsr_r_vw 1717)
  (UNSPEC_QDSP6_Q6S2_lsl_r_vw 1718)
  (UNSPEC_QDSP6_Q6S2_vrndpackwh 1719)
  (UNSPEC_QDSP6_Q6S2_vrndpackwhs 1720)
  (UNSPEC_QDSP6_Q6S2_vsxtbh 1721)
  (UNSPEC_QDSP6_Q6S2_vzxtbh 1722)
  (UNSPEC_QDSP6_Q6S2_vsathub 1723)
  (UNSPEC_QDSP6_Q6S2_svsathub 1724)
  (UNSPEC_QDSP6_Q6S2_svsathb 1725)
  (UNSPEC_QDSP6_Q6S2_vsathb 1726)
  (UNSPEC_QDSP6_Q6S2_vtrunohb 1727)
  (UNSPEC_QDSP6_Q6S2_vtrunewh 1728)
  (UNSPEC_QDSP6_Q6S2_vtrunowh 1729)
  (UNSPEC_QDSP6_Q6S2_vtrunehb 1730)
  (UNSPEC_QDSP6_Q6S2_vsxthw 1731)
  (UNSPEC_QDSP6_Q6S2_vzxthw 1732)
  (UNSPEC_QDSP6_Q6S2_vsatwh 1733)
  (UNSPEC_QDSP6_Q6S2_vsatwuh 1734)
  (UNSPEC_QDSP6_Q6S2_packhl 1735)
  (UNSPEC_QDSP6_Q6A2_swiz 1736)
  (UNSPEC_QDSP6_Q6S2_vsathub_nopack 1737)
  (UNSPEC_QDSP6_Q6S2_vsathb_nopack 1738)
  (UNSPEC_QDSP6_Q6S2_vsatwh_nopack 1739)
  (UNSPEC_QDSP6_Q6S2_vsatwuh_nopack 1740)
  (UNSPEC_QDSP6_Q6S2_shuffob 1741)
  (UNSPEC_QDSP6_Q6S2_shuffeb 1742)
  (UNSPEC_QDSP6_Q6S2_shuffoh 1743)
  (UNSPEC_QDSP6_Q6S2_shuffeh 1744)
  (UNSPEC_QDSP6_Q6S4_parity 1745)
  (UNSPEC_QDSP6_Q6S2_parityp 1746)
  (UNSPEC_QDSP6_Q6S2_lfsp 1747)
  (UNSPEC_QDSP6_Q6S2_clbnorm 1748)
  (UNSPEC_QDSP6_Q6S4_clbaddi 1749)
  (UNSPEC_QDSP6_Q6S4_clbpnorm 1750)
  (UNSPEC_QDSP6_Q6S4_clbpaddi 1751)
  (UNSPEC_QDSP6_Q6S2_clb 1752)
  (UNSPEC_QDSP6_Q6S2_cl0 1753)
  (UNSPEC_QDSP6_Q6S2_cl1 1754)
  (UNSPEC_QDSP6_Q6S2_clbp 1755)
  (UNSPEC_QDSP6_Q6S2_cl0p 1756)
  (UNSPEC_QDSP6_Q6S2_cl1p 1757)
  (UNSPEC_QDSP6_Q6S2_brev 1758)
  (UNSPEC_QDSP6_Q6S2_brevp 1759)
  (UNSPEC_QDSP6_Q6S2_ct0 1760)
  (UNSPEC_QDSP6_Q6S2_ct1 1761)
  (UNSPEC_QDSP6_Q6S2_ct0p 1762)
  (UNSPEC_QDSP6_Q6S2_ct1p 1763)
  (UNSPEC_QDSP6_Q6S2_interleave 1764)
  (UNSPEC_QDSP6_Q6S2_deinterleave 1765)
  (UNSPEC_QDSP6_Q6dep_S2_packhl 1766)
  (UNSPEC_QDSP6_Q6dep_A2_addsat 1767)
  (UNSPEC_QDSP6_Q6dep_A2_subsat 1768)
])


(define_expand "qdsp6_builtin_Q6C2_cmpeq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpeq))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpeq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpeq))]
  ""
  "%0=cmp.eq(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgt))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgt))]
  ""
  "%0=cmp.gt(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgtu))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgtu))]
  ""
  "%0=cmp.gtu(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpeqp"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpeqp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpeqp"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpeqp))]
  ""
  "%0=cmp.eq(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgtp"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgtp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgtp"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgtp))]
  ""
  "%0=cmp.gt(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgtup"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgtup))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgtup"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpgtup))]
  ""
  "%0=cmp.gtu(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_rcmpeqi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_rcmpeqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_cmp_eq_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_R_cmp_eq_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_rcmpeqi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_rcmpeqi))]
  "TARGET_V4_FEATURES"
  "%0=cmp.eq(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_rcmpneqi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_rcmpneqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_cmp_eq_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_R_cmp_eq_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_rcmpneqi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_rcmpneqi))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.eq(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_rcmpeq"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_rcmpeq))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_rcmpeq"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_rcmpeq))]
  "TARGET_V4_FEATURES"
  "%0=cmp.eq(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_rcmpneq"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_rcmpneq))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_rcmpneq"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_rcmpneq))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.eq(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_bitsset"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_bitsset))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_bitsset"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_bitsset))]
  "TARGET_V2_FEATURES"
  "%0=bitsset(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_bitsclr"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_bitsclr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_bitsclr"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_bitsclr))]
  "TARGET_V2_FEATURES"
  "%0=bitsclr(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C4_nbitsset"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_nbitsset))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_nbitsset"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_nbitsset))]
  "TARGET_V4_FEATURES"
  "%0=!bitsset(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C4_nbitsclr"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_nbitsclr))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_nbitsclr"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_nbitsclr))]
  "TARGET_V4_FEATURES"
  "%0=!bitsclr(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpeqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C2_cmpeqi))]
  ""
  {
    if(TARGET_V2_FEATURES){
      if(GET_CODE (operands[2]) != CONST_INT){
        error("non-constant integer passed to argument 2 of Q6_p_cmp_eq_RI intrinsic");
      }
      if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is10")){
        error("argument 2 of Q6_p_cmp_eq_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
      }
    }
    else {
      if(GET_CODE (operands[2]) != CONST_INT){
        error("non-constant integer passed to argument 2 of Q6_p_cmp_eq_RI intrinsic");
      }
      if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
        error("argument 2 of Q6_p_cmp_eq_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
      }
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpeqi_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C2_cmpeqi))]
  "TARGET_V2_FEATURES"
  "%0=cmp.eq(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6C2_cmpeqi_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_cmpeqi))]
  "!TARGET_V2_FEATURES"
  "%0=cmp.eq(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C2_cmpgti))]
  ""
  {
    if(TARGET_V2_FEATURES){
      if(GET_CODE (operands[2]) != CONST_INT){
        error("non-constant integer passed to argument 2 of Q6_p_cmp_gt_RI intrinsic");
      }
      if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is10")){
        error("argument 2 of Q6_p_cmp_gt_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
      }
    }
    else {
      if(GET_CODE (operands[2]) != CONST_INT){
        error("non-constant integer passed to argument 2 of Q6_p_cmp_gt_RI intrinsic");
      }
      if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
        error("argument 2 of Q6_p_cmp_gt_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
      }
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgti_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C2_cmpgti))]
  "TARGET_V2_FEATURES"
  "%0=cmp.gt(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6C2_cmpgti_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_cmpgti))]
  "!TARGET_V2_FEATURES"
  "%0=cmp.gt(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu9")
        ] UNSPEC_QDSP6_Q6C2_cmpgtui))]
  ""
  {
    if(TARGET_V2_FEATURES){
      if(GET_CODE (operands[2]) != CONST_INT){
        error("non-constant integer passed to argument 2 of Q6_p_cmp_gtu_RI intrinsic");
      }
      if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu9")){
        error("argument 2 of Q6_p_cmp_gtu_RI intrinsic cannot be encoded as u9 immediate -- FIXME: can it be extended?");
      }
    }
    else {
      if(GET_CODE (operands[2]) != CONST_INT){
        error("non-constant integer passed to argument 2 of Q6_p_cmp_gtu_RI intrinsic");
      }
      if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu8")){
        error("argument 2 of Q6_p_cmp_gtu_RI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
      }
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgtui_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu9")
        ] UNSPEC_QDSP6_Q6C2_cmpgtui))]
  "TARGET_V2_FEATURES"
  "%0=cmp.gtu(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6C2_cmpgtui_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6C2_cmpgtui))]
  "!TARGET_V2_FEATURES"
  "%0=cmp.gtu(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgei"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_cmpgei))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmp_ge_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_cmp_ge_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgei"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_cmpgei))]
  ""
  "%0=cmp.ge(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpgeui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6C2_cmpgeui))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmp_geu_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu8")){
      error("argument 2 of Q6_p_cmp_geu_RI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpgeui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6C2_cmpgeui))]
  ""
  "%0=cmp.geu(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmplt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmplt))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmplt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmplt))]
  "TARGET_V2_FEATURES"
  "%0=cmp.lt(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_cmpltu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpltu))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_cmpltu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_cmpltu))]
  "TARGET_V2_FEATURES"
  "%0=cmp.ltu(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_bitsclri"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6C2_bitsclri))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_bitsclr_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_p_bitsclr_RI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_bitsclri"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6C2_bitsclri))]
  "TARGET_V2_FEATURES"
  "%0=bitsclr(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C4_nbitsclri"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6C4_nbitsclri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_bitsclr_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_p_bitsclr_RI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C4_nbitsclri"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6C4_nbitsclri))]
  "TARGET_V4_FEATURES"
  "%0=!bitsclr(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C4_cmpneqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C4_cmpneqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmp_eq_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is10")){
      error("argument 2 of Q6_p_cmp_eq_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C4_cmpneqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C4_cmpneqi))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.eq(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C4_cmpltei"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C4_cmpltei))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmp_gt_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is10")){
      error("argument 2 of Q6_p_cmp_gt_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C4_cmpltei"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6C4_cmpltei))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.gt(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C4_cmplteui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu9")
        ] UNSPEC_QDSP6_Q6C4_cmplteui))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmp_gtu_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu9")){
      error("argument 2 of Q6_p_cmp_gtu_RI intrinsic cannot be encoded as u9 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C4_cmplteui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu9")
        ] UNSPEC_QDSP6_Q6C4_cmplteui))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.gtu(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C4_cmpneq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_cmpneq))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_cmpneq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_cmpneq))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.eq(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C4_cmplte"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_cmplte))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_cmplte"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_cmplte))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.gt(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C4_cmplteu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_cmplteu))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_cmplteu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C4_cmplteu))]
  "TARGET_V4_FEATURES"
  "%0=!cmp.gtu(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_and"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_and_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_and))]
  "TARGET_V2_FEATURES"
  "%0=and(%1,%2)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_and_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_and))]
  "!TARGET_V2_FEATURES"
  "%0=and(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_or"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_or_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_or))]
  "TARGET_V2_FEATURES"
  "%0=or(%1,%2)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_or_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_or))]
  "!TARGET_V2_FEATURES"
  "%0=or(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_xor"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_xor))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_xor_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_xor))]
  "TARGET_V2_FEATURES"
  "%0=xor(%1,%2)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_xor_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_xor))]
  "!TARGET_V2_FEATURES"
  "%0=xor(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_andn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_andn))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_andn_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_andn))]
  "TARGET_V2_FEATURES"
  "%0=and(%1,!%2)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_andn_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_andn))]
  "!TARGET_V2_FEATURES"
  "%0=and(%1,!%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_not"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_not))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_not_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_not))]
  "TARGET_V2_FEATURES"
  "%0=not(%1)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_not_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_not))]
  "!TARGET_V2_FEATURES"
  "%0=not(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_orn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_orn))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_orn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_orn))]
  "TARGET_V2_FEATURES"
  "%0=or(%1,!%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_and_and"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_and))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_and_and"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_and))]
  "TARGET_V4_FEATURES"
  "%0=and(%1,and(%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_and_or"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_or))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_and_or"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_or))]
  "TARGET_V4_FEATURES"
  "%0=and(%1,or(%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_or_and"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_and))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_or_and"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_and))]
  "TARGET_V4_FEATURES"
  "%0=or(%1,and(%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_or_or"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_or))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_or_or"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_or))]
  "TARGET_V4_FEATURES"
  "%0=or(%1,or(%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_and_andn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_andn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_and_andn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_andn))]
  "TARGET_V4_FEATURES"
  "%0=and(%1,and(%2,!%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_and_orn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_orn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_and_orn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_and_orn))]
  "TARGET_V4_FEATURES"
  "%0=and(%1,or(%2,!%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_or_andn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_andn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_or_andn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_andn))]
  "TARGET_V4_FEATURES"
  "%0=or(%1,and(%2,!%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C4_or_orn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_orn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C4_or_orn"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C4_or_orn))]
  "TARGET_V4_FEATURES"
  "%0=or(%1,or(%2,!%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C2_pxfer_map"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_pxfer_map))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_pxfer_map"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_pxfer_map))]
  "TARGET_V2_FEATURES"
  "%0=%1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6C2_any8"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_any8))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_any8_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_any8))]
  "TARGET_V2_FEATURES"
  "%0=any8(%1)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_any8_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_any8))]
  "!TARGET_V2_FEATURES"
  "%0=any8(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_all8"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_all8))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_all8_v2"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_all8))]
  "TARGET_V2_FEATURES"
  "%0=all8(%1)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6C2_all8_v1"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_all8))]
  "!TARGET_V2_FEATURES"
  "%0=all8(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_vitpack"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_vitpack))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_vitpack"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:QI 2 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_vitpack))]
  ""
  "%0=vitpack(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_mux"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_mux))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_mux"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_mux))]
  ""
  "%0=mux(%1,%2,%3)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_muxii"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "immediate_operand" "Is8")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_muxii))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_mux_pII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_R_mux_pII intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_mux_pII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is8")){
      error("argument 3 of Q6_R_mux_pII intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_muxii"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "immediate_operand" "Is8")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_muxii))]
  "TARGET_V2_FEATURES"
  "%0=mux(%1,#%2,#%3)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_muxir"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_muxir))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_mux_pRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is8")){
      error("argument 3 of Q6_R_mux_pRI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_muxir"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6C2_muxir))]
  "TARGET_V2_FEATURES"
  "%0=mux(%1,%2,#%3)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_muxri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "immediate_operand" "Is8")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_muxri))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_mux_pIR intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_R_mux_pIR intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C2_muxri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:SI 2 "immediate_operand" "Is8")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_muxri))]
  "TARGET_V2_FEATURES"
  "%0=mux(%1,#%2,%3)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C2_vmux"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_vmux))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_vmux"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_vmux))]
  ""
  "%P0=vmux(%1,%P2,%P3)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C2_mask"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_mask))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_mask"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_mask))]
  ""
  "%P0=mask(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmpbeq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpbeq))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmpbeq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpbeq))]
  ""
  "%0=vcmpb.eq(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpbeqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6A4_vcmpbeqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_vcmpb_eq_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu8")){
      error("argument 2 of Q6_p_vcmpb_eq_PI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpbeqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6A4_vcmpbeqi))]
  "TARGET_V4_FEATURES"
  "%0=vcmpb.eq(%P1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpbeq_any"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpbeq_any))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpbeq_any"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpbeq_any))]
  "TARGET_V4_FEATURES"
  "%0=any8(vcmpb.eq(%P1,%P2))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmpbgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpbgtu))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmpbgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpbgtu))]
  ""
  "%0=vcmpb.gtu(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpbgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpbgtui))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpbgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpbgtui))]
  "TARGET_V4_FEATURES"
  "%0=vcmpb.gtu(%P1,#u7)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpbgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpbgt))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpbgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpbgt))]
  "TARGET_V4_FEATURES"
  "%0=vcmpb.gt(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpbgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpbgti))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_vcmpb_gt_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_vcmpb_gt_PI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpbgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpbgti))]
  "TARGET_V4_FEATURES"
  "%0=vcmpb.gt(%P1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpbeq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbeq))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpbeq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbeq))]
  "TARGET_V4_FEATURES"
  "%0=cmpb.eq(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpbeqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6A4_cmpbeqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmpb_eq_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu8")){
      error("argument 2 of Q6_p_cmpb_eq_RI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpbeqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6A4_cmpbeqi))]
  "TARGET_V4_FEATURES"
  "%0=cmpb.eq(%1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpbgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbgtu))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpbgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbgtu))]
  "TARGET_V4_FEATURES"
  "%0=cmpb.gtu(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpbgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbgtui))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpbgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbgtui))]
  "TARGET_V4_FEATURES"
  "%0=cmpb.gtu(%1,#u7)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpbgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbgt))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpbgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpbgt))]
  "TARGET_V4_FEATURES"
  "%0=cmpb.gt(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpbgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_cmpbgti))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmpb_gt_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_cmpb_gt_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpbgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_cmpbgti))]
  "TARGET_V4_FEATURES"
  "%0=cmpb.gt(%1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmpheq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpheq))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmpheq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpheq))]
  ""
  "%0=vcmph.eq(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmphgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmphgt))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmphgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmphgt))]
  ""
  "%0=vcmph.gt(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmphgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmphgtu))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmphgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmphgtu))]
  ""
  "%0=vcmph.gtu(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpheqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpheqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_vcmph_eq_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_vcmph_eq_PI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpheqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpheqi))]
  "TARGET_V4_FEATURES"
  "%0=vcmph.eq(%P1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmphgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmphgti))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_vcmph_gt_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_vcmph_gt_PI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmphgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmphgti))]
  "TARGET_V4_FEATURES"
  "%0=vcmph.gt(%P1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmphgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmphgtui))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmphgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmphgtui))]
  "TARGET_V4_FEATURES"
  "%0=vcmph.gtu(%P1,#u7)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpheq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpheq))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpheq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmpheq))]
  "TARGET_V4_FEATURES"
  "%0=cmph.eq(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cmphgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmphgt))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmphgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmphgt))]
  "TARGET_V4_FEATURES"
  "%0=cmph.gt(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cmphgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmphgtu))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmphgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmphgtu))]
  "TARGET_V4_FEATURES"
  "%0=cmph.gtu(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cmpheqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_cmpheqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmph_eq_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_cmph_eq_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmpheqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_cmpheqi))]
  "TARGET_V4_FEATURES"
  "%0=cmph.eq(%1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_cmphgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_cmphgti))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_cmph_gt_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_cmph_gt_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmphgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_cmphgti))]
  "TARGET_V4_FEATURES"
  "%0=cmph.gt(%1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_cmphgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmphgtui))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cmphgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cmphgtui))]
  "TARGET_V4_FEATURES"
  "%0=cmph.gtu(%1,#u7)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmpweq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpweq))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmpweq"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpweq))]
  ""
  "%0=vcmpw.eq(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmpwgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpwgt))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmpwgt"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpwgt))]
  ""
  "%0=vcmpw.gt(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vcmpwgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpwgtu))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vcmpwgtu"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vcmpwgtu))]
  ""
  "%0=vcmpw.gtu(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpweqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpweqi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_vcmpw_eq_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_vcmpw_eq_PI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpweqi"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpweqi))]
  "TARGET_V4_FEATURES"
  "%0=vcmpw.eq(%P1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpwgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpwgti))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_vcmpw_gt_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_p_vcmpw_gt_PI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpwgti"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_vcmpwgti))]
  "TARGET_V4_FEATURES"
  "%0=vcmpw.gt(%P1,#%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_vcmpwgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpwgtui))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vcmpwgtui"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vcmpwgtui))]
  "TARGET_V4_FEATURES"
  "%0=vcmpw.gtu(%P1,#u7)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_boundscheck"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_boundscheck))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_boundscheck"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_boundscheck))]
  "TARGET_V4_FEATURES"
  "%0=boundscheck(%1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A4_tlbmatch"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_tlbmatch))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_tlbmatch"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_tlbmatch))]
  "TARGET_V4_FEATURES"
  "%0=tlbmatch(%P1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6C2_tfrpr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_tfrpr))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_tfrpr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:QI 1 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6C2_tfrpr))]
  ""
  "%0=%1"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6C2_tfrrp"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_tfrrp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6C2_tfrrp"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6C2_tfrrp))]
  ""
  "%0=%1"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_machisi3_hh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hh_s0))]
  ""
  "%0+=mpy(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_machisi3_hh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hh_s1))]
  ""
  "%0+=mpy(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hl_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_machisi3_hl(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hl_s0))]
  ""
  "%0+=mpy(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hl_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_machisi3_hl_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_hl_s1))]
  ""
  "%0+=mpy(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_lh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_machisi3_lh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_lh_s0))]
  ""
  "%0+=mpy(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_lh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_machisi3_lh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_lh_s1))]
  ""
  "%0+=mpy(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_ll_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_machisi3_ll(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_ll_s0))]
  ""
  "%0+=mpy(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_ll_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_machisi3_ll_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_ll_s1))]
  ""
  "%0+=mpy(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mnachisi3_hh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hh_s0))]
  ""
  "%0-=mpy(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mnachisi3_hh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hh_s1))]
  ""
  "%0-=mpy(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hl_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_mnachisi3_hl(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hl_s0))]
  ""
  "%0-=mpy(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hl_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_mnachisi3_hl_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_hl_s1))]
  ""
  "%0-=mpy(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_lh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_mnachisi3_lh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_lh_s0))]
  ""
  "%0-=mpy(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_lh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_mnachisi3_lh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_lh_s1))]
  ""
  "%0-=mpy(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_ll_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_mnachisi3_ll(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_ll_s0))]
  ""
  "%0-=mpy(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_ll_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_mnachisi3_ll_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_ll_s1))]
  ""
  "%0-=mpy(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ssmachisi3_hh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hh_s0))]
  ""
  "%0+=mpy(%2.h,%3.h):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ssmachisi3_hh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hh_s1))]
  ""
  "%0+=mpy(%2.h,%3.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hl_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmachisi3_hl(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hl_s0))]
  ""
  "%0+=mpy(%2.h,%3.l):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hl_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmachisi3_hl_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_hl_s1))]
  ""
  "%0+=mpy(%2.h,%3.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_lh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmachisi3_lh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_lh_s0))]
  ""
  "%0+=mpy(%2.l,%3.h):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_lh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmachisi3_lh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_lh_s1))]
  ""
  "%0+=mpy(%2.l,%3.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_ll_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmachisi3_ll(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_ll_s0))]
  ""
  "%0+=mpy(%2.l,%3.l):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_acc_sat_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_ll_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmachisi3_ll_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_acc_sat_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_acc_sat_ll_s1))]
  ""
  "%0+=mpy(%2.l,%3.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ssmnachisi3_hh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hh_s0))]
  ""
  "%0-=mpy(%2.h,%3.h):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ssmnachisi3_hh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hh_s1))]
  ""
  "%0-=mpy(%2.h,%3.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hl_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmnachisi3_hl(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hl_s0))]
  ""
  "%0-=mpy(%2.h,%3.l):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hl_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmnachisi3_hl_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_hl_s1))]
  ""
  "%0-=mpy(%2.h,%3.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_lh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmnachisi3_lh(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_lh_s0))]
  ""
  "%0-=mpy(%2.l,%3.h):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_lh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmnachisi3_lh_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_lh_s1))]
  ""
  "%0-=mpy(%2.l,%3.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_ll_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmnachisi3_ll(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_ll_s0))]
  ""
  "%0-=mpy(%2.l,%3.l):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_nac_sat_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_ll_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      rtx op3 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_move_insn(op3, gen_lowpart(HImode, operands[3]));
      operands[3] = op3;
      emit_insn(gen_ssmnachisi3_ll_s1(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_nac_sat_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_nac_sat_ll_s1))]
  ""
  "%0-=mpy(%2.l,%3.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mulhisi3_hh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hh_s0))]
  ""
  "%0=mpy(%1.h,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mulhisi3_hh_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hh_s1))]
  ""
  "%0=mpy(%1.h,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hl_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_mulhisi3_hl(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hl_s0))]
  ""
  "%0=mpy(%1.h,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hl_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_mulhisi3_hl_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_hl_s1))]
  ""
  "%0=mpy(%1.h,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_lh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_mulhisi3_lh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_lh_s0))]
  ""
  "%0=mpy(%1.l,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_lh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_mulhisi3_lh_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_lh_s1))]
  ""
  "%0=mpy(%1.l,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_ll_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_mulhisi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_ll_s0))]
  ""
  "%0=mpy(%1.l,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_ll_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_mulhisi3_ll_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_ll_s1))]
  ""
  "%0=mpy(%1.l,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ssmulhisi3_hh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hh_s0))]
  ""
  "%0=mpy(%1.h,%2.h):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ssmulhisi3_hh_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hh_s1))]
  ""
  "%0=mpy(%1.h,%2.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hl_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmulhisi3_hl(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hl_s0))]
  ""
  "%0=mpy(%1.h,%2.l):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hl_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmulhisi3_hl_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_hl_s1))]
  ""
  "%0=mpy(%1.h,%2.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_lh_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_ssmulhisi3_lh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_lh_s0))]
  ""
  "%0=mpy(%1.l,%2.h):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_lh_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_ssmulhisi3_lh_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_lh_s1))]
  ""
  "%0=mpy(%1.l,%2.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_ll_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmulhisi3_ll(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_ll_s0))]
  ""
  "%0=mpy(%1.l,%2.l):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_ll_s1))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssmulhisi3_ll_s1(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_ll_s1))]
  ""
  "%0=mpy(%1.l,%2.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hh_s0))]
  ""
  "%0=mpy(%1.h,%2.h):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hh_s1))]
  ""
  "%0=mpy(%1.h,%2.h):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hl_s0))]
  ""
  "%0=mpy(%1.h,%2.l):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_hl_s1))]
  ""
  "%0=mpy(%1.h,%2.l):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_lh_s0))]
  ""
  "%0=mpy(%1.l,%2.h):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_lh_s1))]
  ""
  "%0=mpy(%1.l,%2.h):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_ll_s0))]
  ""
  "%0=mpy(%1.l,%2.l):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_rnd_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_rnd_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_rnd_ll_s1))]
  ""
  "%0=mpy(%1.l,%2.l):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hh_s0))]
  ""
  "%0=mpy(%1.h,%2.h):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hh_s1))]
  ""
  "%0=mpy(%1.h,%2.h):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hl_s0))]
  ""
  "%0=mpy(%1.h,%2.l):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_hl_s1))]
  ""
  "%0=mpy(%1.h,%2.l):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_lh_s0))]
  ""
  "%0=mpy(%1.l,%2.h):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_lh_s1))]
  ""
  "%0=mpy(%1.l,%2.h):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_ll_s0))]
  ""
  "%0=mpy(%1.l,%2.l):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_sat_rnd_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_sat_rnd_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_sat_rnd_ll_s1))]
  ""
  "%0=mpy(%1.l,%2.l):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hh_s0))]
  ""
  "%P0+=mpy(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hh_s1))]
  ""
  "%P0+=mpy(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hl_s0))]
  ""
  "%P0+=mpy(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_hl_s1))]
  ""
  "%P0+=mpy(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_lh_s0))]
  ""
  "%P0+=mpy(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_lh_s1))]
  ""
  "%P0+=mpy(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_ll_s0))]
  ""
  "%P0+=mpy(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_acc_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_acc_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_acc_ll_s1))]
  ""
  "%P0+=mpy(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hh_s0))]
  ""
  "%P0-=mpy(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hh_s1))]
  ""
  "%P0-=mpy(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hl_s0))]
  ""
  "%P0-=mpy(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_hl_s1))]
  ""
  "%P0-=mpy(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_lh_s0))]
  ""
  "%P0-=mpy(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_lh_s1))]
  ""
  "%P0-=mpy(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_ll_s0))]
  ""
  "%P0-=mpy(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_nac_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_nac_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_nac_ll_s1))]
  ""
  "%P0-=mpy(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hh_s0))]
  ""
  "%P0=mpy(%1.h,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hh_s1))]
  ""
  "%P0=mpy(%1.h,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hl_s0))]
  ""
  "%P0=mpy(%1.h,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_hl_s1))]
  ""
  "%P0=mpy(%1.h,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_lh_s0))]
  ""
  "%P0=mpy(%1.l,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_lh_s1))]
  ""
  "%P0=mpy(%1.l,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_ll_s0))]
  ""
  "%P0=mpy(%1.l,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_ll_s1))]
  ""
  "%P0=mpy(%1.l,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hh_s0))]
  ""
  "%P0=mpy(%1.h,%2.h):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hh_s1))]
  ""
  "%P0=mpy(%1.h,%2.h):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hl_s0))]
  ""
  "%P0=mpy(%1.h,%2.l):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_hl_s1))]
  ""
  "%P0=mpy(%1.h,%2.l):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_lh_s0))]
  ""
  "%P0=mpy(%1.l,%2.h):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_lh_s1))]
  ""
  "%P0=mpy(%1.l,%2.h):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_ll_s0))]
  ""
  "%P0=mpy(%1.l,%2.l):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyd_rnd_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyd_rnd_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyd_rnd_ll_s1))]
  ""
  "%P0=mpy(%1.l,%2.l):<<1:rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hh_s0))]
  ""
  "%0+=mpyu(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hh_s1))]
  ""
  "%0+=mpyu(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hl_s0))]
  ""
  "%0+=mpyu(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_hl_s1))]
  ""
  "%0+=mpyu(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_lh_s0))]
  ""
  "%0+=mpyu(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_lh_s1))]
  ""
  "%0+=mpyu(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_ll_s0))]
  ""
  "%0+=mpyu(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_acc_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_acc_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_acc_ll_s1))]
  ""
  "%0+=mpyu(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hh_s0))]
  ""
  "%0-=mpyu(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hh_s1))]
  ""
  "%0-=mpyu(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hl_s0))]
  ""
  "%0-=mpyu(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_hl_s1))]
  ""
  "%0-=mpyu(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_lh_s0))]
  ""
  "%0-=mpyu(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_lh_s1))]
  ""
  "%0-=mpyu(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_ll_s0))]
  ""
  "%0-=mpyu(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_nac_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_nac_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_nac_ll_s1))]
  ""
  "%0-=mpyu(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_hh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hh_s0))]
  ""
  "%0=mpyu(%1.h,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_hh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hh_s1))]
  ""
  "%0=mpyu(%1.h,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_hl_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hl_s0))]
  ""
  "%0=mpyu(%1.h,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_hl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_hl_s1))]
  ""
  "%0=mpyu(%1.h,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_lh_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_lh_s0))]
  ""
  "%0=mpyu(%1.l,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_lh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_lh_s1))]
  ""
  "%0=mpyu(%1.l,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_ll_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_ll_s0))]
  ""
  "%0=mpyu(%1.l,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_ll_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_ll_s1))]
  ""
  "%0=mpyu(%1.l,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hh_s0))]
  ""
  "%P0+=mpyu(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hh_s1))]
  ""
  "%P0+=mpyu(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hl_s0))]
  ""
  "%P0+=mpyu(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_hl_s1))]
  ""
  "%P0+=mpyu(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_lh_s0))]
  ""
  "%P0+=mpyu(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_lh_s1))]
  ""
  "%P0+=mpyu(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_ll_s0))]
  ""
  "%P0+=mpyu(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_acc_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_acc_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_acc_ll_s1))]
  ""
  "%P0+=mpyu(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hh_s0))]
  ""
  "%P0-=mpyu(%2.h,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hh_s1))]
  ""
  "%P0-=mpyu(%2.h,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hl_s0))]
  ""
  "%P0-=mpyu(%2.h,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_hl_s1))]
  ""
  "%P0-=mpyu(%2.h,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_lh_s0))]
  ""
  "%P0-=mpyu(%2.l,%3.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_lh_s1))]
  ""
  "%P0-=mpyu(%2.l,%3.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_ll_s0))]
  ""
  "%P0-=mpyu(%2.l,%3.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_nac_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_nac_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_nac_ll_s1))]
  ""
  "%P0-=mpyu(%2.l,%3.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_hh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hh_s0))]
  ""
  "%P0=mpyu(%1.h,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_hh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hh_s1))]
  ""
  "%P0=mpyu(%1.h,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_hl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hl_s0))]
  ""
  "%P0=mpyu(%1.h,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_hl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_hl_s1))]
  ""
  "%P0=mpyu(%1.h,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_lh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_lh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_lh_s0))]
  ""
  "%P0=mpyu(%1.l,%2.h)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_lh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_lh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_lh_s1))]
  ""
  "%P0=mpyu(%1.l,%2.h):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_ll_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_ll_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_ll_s0))]
  ""
  "%P0=mpyu(%1.l,%2.l)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyud_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_ll_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyud_ll_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyud_ll_s1))]
  ""
  "%P0=mpyu(%1.l,%2.l):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpysmi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Im9")
        ] UNSPEC_QDSP6_Q6M2_mpysmi))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_mpyi_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Im9")){
      error("argument 2 of Q6_R_mpyi_RI intrinsic cannot be encoded as m9 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpysmi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Im9")
        ] UNSPEC_QDSP6_Q6M2_mpysmi))]
  "TARGET_V2_FEATURES"
  "%0=mpyi(%1,#%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_macsip"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6M2_macsip))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_mpyiacc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu8")){
      error("argument 3 of Q6_R_mpyiacc_RI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_macsip"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6M2_macsip))]
  "TARGET_V2_FEATURES"
  "%0+=mpyi(%2,#%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_macsin"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6M2_macsin))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_mpyinac_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu8")){
      error("argument 3 of Q6_R_mpyinac_RI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_macsin"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu8")
        ] UNSPEC_QDSP6_Q6M2_macsin))]
  "TARGET_V2_FEATURES"
  "%0-=mpyi(%2,#%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyss_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mulsidi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyss_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_s0))]
  ""
  "%P0=mpy(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyss_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_acc_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_macsidi3(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyss_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_acc_s0))]
  ""
  "%P0+=mpy(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyss_nac_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_nac_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mnacsidi3(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyss_nac_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_nac_s0))]
  ""
  "%P0-=mpy(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyuu_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyuu_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_umulsidi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyuu_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyuu_s0))]
  ""
  "%P0=mpyu(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyuu_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyuu_acc_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_umacsidi3(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyuu_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyuu_acc_s0))]
  ""
  "%P0+=mpyu(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyuu_nac_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyuu_nac_s0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_umnacsidi3(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyuu_nac_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyuu_nac_s0))]
  ""
  "%P0-=mpyu(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_up"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_up))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_smulsi3_highpart(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_up"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_up))]
  ""
  "%0=mpy(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_up_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_up_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_up_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_up_s1))]
  "TARGET_V4_FEATURES"
  "%0=mpy(%1,%2):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpy_up_s1_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_up_s1_sat))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpy_up_s1_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpy_up_s1_sat))]
  "TARGET_V4_FEATURES"
  "%0=mpy(%1,%2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyu_up"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_up))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_umulsi3_highpart(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyu_up"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyu_up))]
  ""
  "%0=mpyu(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpysu_up"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpysu_up))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpysu_up"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpysu_up))]
  "TARGET_V4_FEATURES"
  "%0=mpysu(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_dpmpyss_rnd_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_rnd_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_dpmpyss_rnd_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_dpmpyss_rnd_s0))]
  ""
  "%0=mpy(%1,%2):rnd"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_mac_up_s1_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mac_up_s1_sat))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_mac_up_s1_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mac_up_s1_sat))]
  "TARGET_V4_FEATURES"
  "%0+=mpy(%2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_nac_up_s1_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_nac_up_s1_sat))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_nac_up_s1_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_nac_up_s1_sat))]
  "TARGET_V4_FEATURES"
  "%0-=mpy(%2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyi))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mulsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyi))]
  ""
  "%0=mpyi(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mpyui"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyui))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_mulsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_mpyui_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyui))]
  "TARGET_V2_FEATURES"
  "%0=mpyui(%1,%2)"
  [(set_attr "type" "X")]
)


(define_insn "qdsp6_unspec_Q6M2_mpyui_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mpyui))]
  "!TARGET_V2_FEATURES"
  "%0=mpyui(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_maci"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_maci))]
  "TARGET_V2_FEATURES"
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_macsi3(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_maci"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_maci))]
  "TARGET_V2_FEATURES"
  "%0+=mpyi(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_acci"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_acci))]
  "TARGET_V2_FEATURES"
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addaccsi3(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_acci"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_acci))]
  "TARGET_V2_FEATURES"
  "%0+=add(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_accii"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6M2_accii))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_addacc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is8")){
      error("argument 3 of Q6_R_addacc_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addaccsi3(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_accii"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6M2_accii))]
  "TARGET_V2_FEATURES"
  "%0+=add(%2,#%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_nacci"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_nacci))]
  "TARGET_V2_FEATURES"
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addnacc1si3(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_nacci"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_nacci))]
  "TARGET_V2_FEATURES"
  "%0-=add(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_naccii"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6M2_naccii))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_addnac_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is8")){
      error("argument 3 of Q6_R_addnac_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addnacc1si3(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_naccii"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6M2_naccii))]
  "TARGET_V2_FEATURES"
  "%0-=add(%2,#%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_subacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_subacc))]
  "TARGET_V2_FEATURES"
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_subacc1si3(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6M2_subacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_subacc))]
  "TARGET_V2_FEATURES"
  "%0+=sub(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_mpyrr_addr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mpyrr_addr))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_mpyrr_addr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mpyrr_addr))]
  "TARGET_V4_FEATURES"
  "%0=add(%2,mpyi(%0,%3))"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_mpyri_addr_u2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Ju6_2")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mpyri_addr_u2))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_add_mpyi_RIR_2,Rs32)) intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'J', "Ju6_2")){
      error("argument 2 of Q6_R_add_mpyi_RIR_2,Rs32)) intrinsic cannot be encoded as u6_2 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M4_mpyri_addr_u2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Ju6_2")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mpyri_addr_u2))]
  "TARGET_V4_FEATURES"
  "%0=add(%1,mpyi(#%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M4_mpyri_addr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6M4_mpyri_addr))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_add_mpyi_RRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_R_add_mpyi_RRI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M4_mpyri_addr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6M4_mpyri_addr))]
  "TARGET_V4_FEATURES"
  "%0=add(%1,mpyi(%2,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M4_mpyri_addi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu6")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6M4_mpyri_addi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_add_mpyi_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu6")){
      error("argument 1 of Q6_R_add_mpyi_IRI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_add_mpyi_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_R_add_mpyi_IRI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M4_mpyri_addi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu6")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6M4_mpyri_addi))]
  "TARGET_V4_FEATURES"
  "%0=add(#%1,mpyi(%2,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M4_mpyrr_addi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu6")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mpyrr_addi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_add_mpyi_IRR intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu6")){
      error("argument 1 of Q6_R_add_mpyi_IRR intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6M4_mpyrr_addi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu6")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_mpyrr_addi))]
  "TARGET_V4_FEATURES"
  "%0=add(#%1,mpyi(%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2s_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2s_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s0))]
  ""
  "%P0=vmpyh(%1,%2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2s_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2s_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s1))]
  ""
  "%P0=vmpyh(%1,%2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2s_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2s_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2s_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2s_s0))]
  ""
  "%P0+=vmpyh(%2,%3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2s_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2s_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2s_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2s_s1))]
  ""
  "%P0+=vmpyh(%2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2su_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2su_s0))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2su_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2su_s0))]
  "TARGET_V4_FEATURES"
  "%P0=vmpyhsu(%1,%2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2su_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2su_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2su_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2su_s1))]
  "TARGET_V4_FEATURES"
  "%P0=vmpyhsu(%1,%2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2su_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2su_s0))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2su_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2su_s0))]
  "TARGET_V4_FEATURES"
  "%P0+=vmpyhsu(%2,%3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2su_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2su_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2su_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2su_s1))]
  "TARGET_V4_FEATURES"
  "%P0+=vmpyhsu(%2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2s_s0pack"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s0pack))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2s_s0pack"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s0pack))]
  "TARGET_V2_FEATURES"
  "%0=vmpyh(%1,%2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2s_s1pack"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s1pack))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2s_s1pack"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2s_s1pack))]
  "TARGET_V2_FEATURES"
  "%0=vmpyh(%1,%2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2))]
  "TARGET_V2_FEATURES"
  "%P0+=vmpyh(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2es_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2es_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2es_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2es_s0))]
  ""
  "%P0=vmpyeh(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmpy2es_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2es_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmpy2es_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmpy2es_s1))]
  ""
  "%P0=vmpyeh(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2es_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2es_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2es_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2es_s0))]
  ""
  "%P0+=vmpyeh(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2es_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2es_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2es_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2es_s1))]
  ""
  "%P0+=vmpyeh(%P2,%P3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vmac2es"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2es))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vmac2es"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vmac2es))]
  "TARGET_V2_FEATURES"
  "%P0+=vmpyeh(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrmac_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrmac_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrmac_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrmac_s0))]
  ""
  "%P0+=vrmpyh(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrmpy_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrmpy_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrmpy_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrmpy_s0))]
  ""
  "%P0=vrmpyh(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vdmpyrs_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpyrs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vdmpyrs_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpyrs_s0))]
  ""
  "%0=vdmpy(%P1,%P2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vdmpyrs_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpyrs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vdmpyrs_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpyrs_s1))]
  ""
  "%0=vdmpy(%P1,%P2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vdmacs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmacs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vdmacs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmacs_s0))]
  ""
  "%P0+=vdmpy(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vdmacs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmacs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vdmacs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmacs_s1))]
  ""
  "%P0+=vdmpy(%P2,%P3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vdmpys_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpys_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vdmpys_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpys_s0))]
  ""
  "%P0=vdmpy(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vdmpys_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpys_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vdmpys_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vdmpys_s1))]
  ""
  "%P0=vdmpy(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpyrs_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpyrs_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrs_s0))]
  ""
  "%0=cmpy(%1,%2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpyrs_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpyrs_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrs_s1))]
  ""
  "%0=cmpy(%1,%2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpyrsc_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrsc_s0))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpyrsc_s0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrsc_s0))]
  "TARGET_V2_FEATURES"
  "%0=cmpy(%1,%2*):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpyrsc_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrsc_s1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpyrsc_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyrsc_s1))]
  "TARGET_V2_FEATURES"
  "%0=cmpy(%1,%2*):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmacs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmacs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacs_s0))]
  ""
  "%P0+=cmpy(%2,%3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmacs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmacs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacs_s1))]
  ""
  "%P0+=cmpy(%2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmacsc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacsc_s0))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmacsc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacsc_s0))]
  "TARGET_V2_FEATURES"
  "%P0+=cmpy(%2,%3*):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmacsc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacsc_s1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmacsc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacsc_s1))]
  "TARGET_V2_FEATURES"
  "%P0+=cmpy(%2,%3*):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpys_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpys_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpys_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpys_s0))]
  ""
  "%P0=cmpy(%1,%2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpys_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpys_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpys_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpys_s1))]
  ""
  "%P0=cmpy(%1,%2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpysc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpysc_s0))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpysc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpysc_s0))]
  "TARGET_V2_FEATURES"
  "%P0=cmpy(%1,%2*):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpysc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpysc_s1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpysc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpysc_s1))]
  "TARGET_V2_FEATURES"
  "%P0=cmpy(%1,%2*):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cnacs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacs_s0))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cnacs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacs_s0))]
  "TARGET_V2_FEATURES"
  "%P0-=cmpy(%2,%3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cnacs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacs_s1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cnacs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacs_s1))]
  "TARGET_V2_FEATURES"
  "%P0-=cmpy(%2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cnacsc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacsc_s0))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cnacsc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacsc_s0))]
  "TARGET_V2_FEATURES"
  "%P0-=cmpy(%2,%3*):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cnacsc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacsc_s1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cnacsc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cnacsc_s1))]
  "TARGET_V2_FEATURES"
  "%P0-=cmpy(%2,%3*):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpys_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpys_s1))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpys_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpys_s1))]
  "TARGET_V3_FEATURES"
  "%P0=vrcmpys(%P1,%2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpys_acc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpys_acc_s1))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpys_acc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpys_acc_s1))]
  "TARGET_V3_FEATURES"
  "%P0+=vrcmpys(%P2,%3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpys_s1rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpys_s1rp))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpys_s1rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpys_s1rp))]
  "TARGET_V3_FEATURES"
  "%0=vrcmpys(%P1,%2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacls_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacls_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_s0))]
  ""
  "%P0+=vmpyweh(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacls_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacls_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_s1))]
  ""
  "%P0+=vmpyweh(%P2,%P3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmachs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmachs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_s0))]
  ""
  "%P0+=vmpywoh(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmachs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmachs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_s1))]
  ""
  "%P0+=vmpywoh(%P2,%P3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyl_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_s0))]
  ""
  "%P0=vmpyweh(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyl_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_s1))]
  ""
  "%P0=vmpyweh(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_s0))]
  ""
  "%P0=vmpywoh(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_s1))]
  ""
  "%P0=vmpywoh(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacls_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacls_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_rs0))]
  ""
  "%P0+=vmpyweh(%P2,%P3):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacls_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacls_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacls_rs1))]
  ""
  "%P0+=vmpyweh(%P2,%P3):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmachs_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmachs_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_rs0))]
  ""
  "%P0+=vmpywoh(%P2,%P3):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmachs_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmachs_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmachs_rs1))]
  ""
  "%P0+=vmpywoh(%P2,%P3):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyl_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyl_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_rs0))]
  ""
  "%P0=vmpyweh(%P1,%P2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyl_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyl_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyl_rs1))]
  ""
  "%P0=vmpyweh(%P1,%P2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyh_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyh_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_rs0))]
  ""
  "%P0=vmpywoh(%P1,%P2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyh_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyh_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyh_rs1))]
  ""
  "%P0=vmpywoh(%P1,%P2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyeh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_s0))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyeh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_s0))]
  "TARGET_V4_FEATURES"
  "%P0=vrmpyweh(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyeh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyeh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_s1))]
  "TARGET_V4_FEATURES"
  "%P0=vrmpyweh(%P1,%P2):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyeh_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_acc_s0))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyeh_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_acc_s0))]
  "TARGET_V4_FEATURES"
  "%P0+=vrmpyweh(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyeh_acc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_acc_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyeh_acc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyeh_acc_s1))]
  "TARGET_V4_FEATURES"
  "%P0+=vrmpyweh(%P2,%P3):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyoh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_s0))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyoh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_s0))]
  "TARGET_V4_FEATURES"
  "%P0=vrmpywoh(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyoh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyoh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_s1))]
  "TARGET_V4_FEATURES"
  "%P0=vrmpywoh(%P1,%P2):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyoh_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_acc_s0))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyoh_acc_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_acc_s0))]
  "TARGET_V4_FEATURES"
  "%P0+=vrmpywoh(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vrmpyoh_acc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_acc_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vrmpyoh_acc_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vrmpyoh_acc_s1))]
  "TARGET_V4_FEATURES"
  "%P0+=vrmpywoh(%P2,%P3):<<1"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_hmmpyl_rs1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyl_rs1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_hmmpyl_rs1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyl_rs1))]
  "TARGET_V2_FEATURES"
  "%0=mpy(%1,%2.l):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_hmmpyh_rs1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyh_rs1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_hmmpyh_rs1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyh_rs1))]
  "TARGET_V2_FEATURES"
  "%0=mpy(%1,%2.h):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_hmmpyl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyl_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_hmmpyl_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyl_s1))]
  "TARGET_V4_FEATURES"
  "%0=mpy(%1,%2.l):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_hmmpyh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyh_s1))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_hmmpyh_s1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_hmmpyh_s1))]
  "TARGET_V4_FEATURES"
  "%0=mpy(%1,%2.h):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmaculs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmaculs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_s0))]
  ""
  "%P0+=vmpyweuh(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmaculs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmaculs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_s1))]
  ""
  "%P0+=vmpyweuh(%P2,%P3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacuhs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacuhs_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_s0))]
  ""
  "%P0+=vmpywouh(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacuhs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacuhs_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_s1))]
  ""
  "%P0+=vmpywouh(%P2,%P3):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyul_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyul_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_s0))]
  ""
  "%P0=vmpyweuh(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyul_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyul_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_s1))]
  ""
  "%P0=vmpyweuh(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyuh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyuh_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_s0))]
  ""
  "%P0=vmpywouh(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyuh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_s1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyuh_s1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_s1))]
  ""
  "%P0=vmpywouh(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmaculs_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmaculs_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_rs0))]
  ""
  "%P0+=vmpyweuh(%P2,%P3):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmaculs_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmaculs_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmaculs_rs1))]
  ""
  "%P0+=vmpyweuh(%P2,%P3):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacuhs_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacuhs_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_rs0))]
  ""
  "%P0+=vmpywouh(%P2,%P3):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmacuhs_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmacuhs_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmacuhs_rs1))]
  ""
  "%P0+=vmpywouh(%P2,%P3):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyul_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyul_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_rs0))]
  ""
  "%P0=vmpyweuh(%P1,%P2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyul_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyul_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyul_rs1))]
  ""
  "%P0=vmpyweuh(%P1,%P2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyuh_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_rs0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyuh_rs0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_rs0))]
  ""
  "%P0=vmpywouh(%P1,%P2):rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_mmpyuh_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_rs1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_mmpyuh_rs1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_mmpyuh_rs1))]
  ""
  "%P0=vmpywouh(%P1,%P2):<<1:rnd:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmaci_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmaci_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmaci_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmaci_s0))]
  ""
  "%P0+=vrcmpyi(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmacr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmacr_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmacr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmacr_s0))]
  ""
  "%P0+=vrcmpyr(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmaci_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmaci_s0c))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmaci_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmaci_s0c))]
  "TARGET_V2_FEATURES"
  "%P0+=vrcmpyi(%P2,%P3*)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmacr_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmacr_s0c))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmacr_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmacr_s0c))]
  "TARGET_V2_FEATURES"
  "%P0+=vrcmpyr(%P2,%P3*)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmaci_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmaci_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmaci_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmaci_s0))]
  ""
  "%P0+=cmpyi(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmacr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacr_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmacr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmacr_s0))]
  ""
  "%P0+=cmpyr(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpyi_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyi_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpyi_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyi_s0))]
  ""
  "%P0=vrcmpyi(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpyr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyr_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpyr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyr_s0))]
  ""
  "%P0=vrcmpyr(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpyi_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyi_s0c))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpyi_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyi_s0c))]
  "TARGET_V2_FEATURES"
  "%P0=vrcmpyi(%P1,%P2*)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vrcmpyr_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyr_s0c))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vrcmpyr_s0c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vrcmpyr_s0c))]
  "TARGET_V2_FEATURES"
  "%P0=vrcmpyr(%P1,%P2*)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpyi_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyi_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpyi_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyi_s0))]
  ""
  "%P0=cmpyi(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_cmpyr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyr_s0))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_cmpyr_s0"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_cmpyr_s0))]
  ""
  "%P0=cmpyr(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_cmpyi_wh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_cmpyi_wh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_cmpyi_wh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_cmpyi_wh))]
  "TARGET_V4_FEATURES"
  "%0=cmpyiwh(%P1,%2):<<1:rnd:sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6M4_cmpyr_wh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_cmpyr_wh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_cmpyr_wh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_cmpyr_wh))]
  "TARGET_V4_FEATURES"
  "%0=cmpyrwh(%P1,%2):<<1:rnd:sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6M2_vcmpy_s0_sat_i"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s0_sat_i))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vcmpy_s0_sat_i"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s0_sat_i))]
  "TARGET_V2_FEATURES"
  "%P0=vcmpyi(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vcmpy_s0_sat_r"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s0_sat_r))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vcmpy_s0_sat_r"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s0_sat_r))]
  "TARGET_V2_FEATURES"
  "%P0=vcmpyr(%P1,%P2):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vcmpy_s1_sat_i"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s1_sat_i))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vcmpy_s1_sat_i"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s1_sat_i))]
  "TARGET_V2_FEATURES"
  "%P0=vcmpyi(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vcmpy_s1_sat_r"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s1_sat_r))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vcmpy_s1_sat_r"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmpy_s1_sat_r))]
  "TARGET_V2_FEATURES"
  "%P0=vcmpyr(%P1,%P2):<<1:sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vcmac_s0_sat_i"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmac_s0_sat_i))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vcmac_s0_sat_i"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmac_s0_sat_i))]
  "TARGET_V2_FEATURES"
  "%P0+=vcmpyi(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vcmac_s0_sat_r"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmac_s0_sat_r))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vcmac_s0_sat_r"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vcmac_s0_sat_r))]
  "TARGET_V2_FEATURES"
  "%P0+=vcmpyr(%P2,%P3):sat"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6S2_vcrotate"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vcrotate))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vcrotate"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vcrotate))]
  "TARGET_V2_FEATURES"
  "%P0=vcrotate(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vrcrotate_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vrcrotate_acc))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vrcrotate_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vrcrotate_acc))]
  "TARGET_V4_FEATURES"
  "%P0+=vrcrotate(%P2,%3,#u2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vrcrotate"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vrcrotate))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vrcrotate"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vrcrotate))]
  "TARGET_V4_FEATURES"
  "%P0=vrcrotate(%P1,%2,#u2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vcnegh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vcnegh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vcnegh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vcnegh))]
  "TARGET_V4_FEATURES"
  "%P0=vcnegh(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vrcnegh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vrcnegh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vrcnegh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vrcnegh))]
  "TARGET_V4_FEATURES"
  "%P0+=vrcnegh(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6M4_pmpyw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_pmpyw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_pmpyw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_pmpyw))]
  "TARGET_V4_FEATURES"
  "%P0=pmpyw(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vpmpyh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vpmpyh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vpmpyh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vpmpyh))]
  "TARGET_V4_FEATURES"
  "%P0=vpmpyh(%1,%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_pmpyw_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_pmpyw_acc))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_pmpyw_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_pmpyw_acc))]
  "TARGET_V4_FEATURES"
  "%P0^=pmpyw(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_vpmpyh_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vpmpyh_acc))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_vpmpyh_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_vpmpyh_acc))]
  "TARGET_V4_FEATURES"
  "%P0^=vpmpyh(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_add"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_add))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_add"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_add))]
  ""
  "%0=add(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_sub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sub))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_subsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_sub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sub))]
  ""
  "%0=sub(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_addsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addsat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addsat_v4"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addsat))]
  "TARGET_V4_FEATURES"
  "%0=add(%1,%2):sat"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_addsat_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addsat))]
  "!TARGET_V4_FEATURES"
  "%0=add(%1,%2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subsat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subsat_v4"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subsat))]
  "TARGET_V4_FEATURES"
  "%0=sub(%1,%2):sat"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_subsat_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subsat))]
  "!TARGET_V4_FEATURES"
  "%0=sub(%1,%2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is16")
        ] UNSPEC_QDSP6_Q6A2_addi))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_add_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is16")){
      error("argument 2 of Q6_R_add_RI intrinsic cannot be encoded as s16 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_addi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is16")
        ] UNSPEC_QDSP6_Q6A2_addi))]
  ""
  "%0=add(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6C4_addipc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6C4_addipc))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_add_pc_I intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu6")){
      error("argument 1 of Q6_R_add_pc_I intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6C4_addipc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6C4_addipc))]
  "TARGET_V4_FEATURES"
  "%0=add(pc,#%1)"
  [(set_attr "type" "CR")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_l16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_ll))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addhi3_ll(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_l16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_ll))]
  ""
  "%0=add(%1.l,%2.l)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_l16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_hl))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addhi3_lh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_l16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_hl))]
  ""
  "%0=add(%1.l,%2.h)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_l16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_sat_ll))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_ssaddhi3_ll(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_l16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_sat_ll))]
  ""
  "%0=add(%1.l,%2.l):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_l16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_sat_hl))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_ssaddhi3_lh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_l16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_l16_sat_hl))]
  ""
  "%0=add(%1.l,%2.h):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_l16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_ll))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_subhi3_ll(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_l16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_ll))]
  ""
  "%0=sub(%1.l,%2.l)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_l16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_hl))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_subhi3_lh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_l16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_hl))]
  ""
  "%0=sub(%1.l,%2.h)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_l16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_sat_ll))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      rtx op2 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_move_insn(op2, gen_lowpart(HImode, operands[2]));
      operands[2] = op2;
      emit_insn(gen_sssubhi3_ll(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_l16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_sat_ll))]
  ""
  "%0=sub(%1.l,%2.l):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_l16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_sat_hl))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_sssubhi3_lh(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_l16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_l16_sat_hl))]
  ""
  "%0=sub(%1.l,%2.h):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_ll))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_ll))]
  ""
  "%0=add(%1.l,%2.l):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_lh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_lh))]
  ""
  "%0=add(%1.l,%2.h):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_hl))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_hl))]
  ""
  "%0=add(%1.h,%2.l):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_hh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_hh))]
  ""
  "%0=add(%1.h,%2.h):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_ll))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_ll))]
  ""
  "%0=add(%1.l,%2.l):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_sat_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_lh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_sat_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_lh))]
  ""
  "%0=add(%1.l,%2.h):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_hl))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_hl))]
  ""
  "%0=add(%1.h,%2.l):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addh_h16_sat_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_hh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addh_h16_sat_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addh_h16_sat_hh))]
  ""
  "%0=add(%1.h,%2.h):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_ll))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_ll))]
  ""
  "%0=sub(%1.l,%2.l):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_lh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_lh))]
  ""
  "%0=sub(%1.l,%2.h):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_hl))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_hl))]
  ""
  "%0=sub(%1.h,%2.l):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_hh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_hh))]
  ""
  "%0=sub(%1.h,%2.h):<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_ll))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_sat_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_ll))]
  ""
  "%0=sub(%1.l,%2.l):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_sat_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_lh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_sat_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_lh))]
  ""
  "%0=sub(%1.l,%2.h):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_hl))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_sat_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_hl))]
  ""
  "%0=sub(%1.h,%2.l):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_subh_h16_sat_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_hh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_subh_h16_sat_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subh_h16_sat_hh))]
  ""
  "%0=sub(%1.h,%2.h):sat:<<16"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_aslh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_aslh))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3(operands[0], operands[1], GEN_INT (16)));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_aslh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_aslh))]
  ""
  "%0=aslh(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_asrh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_asrh))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3(operands[0], operands[1], GEN_INT (16)));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_asrh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_asrh))]
  ""
  "%0=asrh(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_addp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_adddi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_addp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addp))]
  ""
  "%P0=add(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addpsat"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addpsat))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addpsat"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addpsat))]
  "TARGET_V3_FEATURES"
  "%P0=add(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_addsp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addsp))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_addsp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_addsp))]
  "TARGET_V3_FEATURES"
  "%P0=add(%1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_subp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_subdi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_subp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subp))]
  ""
  "%P0=sub(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_addp_c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_addp_c))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_addp_c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_addp_c))]
  "TARGET_V4_FEATURES"
  "%P0=add(%P1,%P2,Px4):carry"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_subp_c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_subp_c))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_subp_c"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_subp_c))]
  "TARGET_V4_FEATURES"
  "%P0=sub(%P1,%P2,Px4):carry"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_neg"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_neg))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_negsi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_neg"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_neg))]
  ""
  "%0=neg(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_negsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_negsat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_negsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_negsat))]
  ""
  "%0=neg(%1):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_abs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_abs))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_abssi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_abs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_abs))]
  ""
  "%0=abs(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_abssat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_abssat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_abssat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_abssat))]
  ""
  "%0=abs(%1):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vconj"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vconj))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vconj"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vconj))]
  "TARGET_V2_FEATURES"
  "%P0=vconj(%P1):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_negp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_negp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_negdi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_negp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_negp))]
  ""
  "%P0=neg(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_absp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_absp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_absdi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_absp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_absp))]
  ""
  "%P0=abs(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_max"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_max))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_smaxsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_max"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_max))]
  ""
  "%0=max(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_maxu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_maxu))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_umaxsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_maxu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_maxu))]
  ""
  "%0=maxu(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_min"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_min))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_sminsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_min"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_min))]
  ""
  "%0=min(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_minu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_minu))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_uminsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_minu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_minu))]
  ""
  "%0=minu(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_maxp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_maxp))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_maxp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_maxp))]
  "TARGET_V3_FEATURES"
  "%P0=max(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_maxup"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_maxup))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_maxup"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_maxup))]
  "TARGET_V3_FEATURES"
  "%P0=maxu(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_minp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_minp))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_minp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_minp))]
  "TARGET_V3_FEATURES"
  "%P0=min(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_minup"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_minup))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_minup"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_minup))]
  "TARGET_V3_FEATURES"
  "%P0=minu(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_tfr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_tfr))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_movsi(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_tfr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_tfr))]
  ""
  "%0=%1"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_tfrsi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Is16")
        ] UNSPEC_QDSP6_Q6A2_tfrsi))]
  ""
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_equals_I intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Is16")){
      error("argument 1 of Q6_R_equals_I intrinsic cannot be encoded as s16 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_movsi(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_tfrsi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Is16")
        ] UNSPEC_QDSP6_Q6A2_tfrsi))]
  ""
  "%0=#%1"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_tfrp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_tfrp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_movdi(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_tfrp_v2"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_tfrp))]
  "TARGET_V2_FEATURES"
  "%P0=%P1"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_tfrp_v1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_tfrp))]
  "!TARGET_V2_FEATURES"
  "%P0=%P1"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_tfrpi"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A2_tfrpi))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_P_equals_I intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Is8")){
      error("argument 1 of Q6_P_equals_I intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_tfrpi"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A2_tfrpi))]
  "TARGET_V2_FEATURES"
  "%P0=#%1"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_zxtb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_zxtb))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(QImode);
      emit_move_insn(op1, gen_lowpart(QImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_zero_extendqisi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_zxtb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_zxtb))]
  ""
  "%0=zxtb(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_sxtb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sxtb))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(QImode);
      emit_move_insn(op1, gen_lowpart(QImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_extendqisi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_sxtb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sxtb))]
  ""
  "%0=sxtb(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_zxth"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_zxth))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_zero_extendhisi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_zxth"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_zxth))]
  ""
  "%0=zxth(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_sxth"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sxth))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      rtx op1 = gen_reg_rtx(HImode);
      emit_move_insn(op1, gen_lowpart(HImode, operands[1]));
      operands[1] = op1;
      emit_insn(gen_extendhisi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_sxth"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sxth))]
  ""
  "%0=sxth(%1)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_combinew"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combinew))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_combinew"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combinew))]
  ""
  "%P0=combine(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_combineri"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_combineri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_combine_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_P_combine_RI intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_combineri"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A4_combineri))]
  "TARGET_V4_FEATURES"
  "%P0=combine(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_combineir"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "immediate_operand" "Is8")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_combineir))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_P_combine_IR intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Is8")){
      error("argument 1 of Q6_P_combine_IR intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_combineir"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "immediate_operand" "Is8")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_combineir))]
  "TARGET_V4_FEATURES"
  "%P0=combine(#%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_combineii"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "immediate_operand" "Is8")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A2_combineii))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_P_combine_II intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Is8")){
      error("argument 1 of Q6_P_combine_II intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_combine_II intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is8")){
      error("argument 2 of Q6_P_combine_II intrinsic cannot be encoded as s8 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_combineii"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "immediate_operand" "Is8")
          (match_operand:SI 2 "immediate_operand" "Is8")
        ] UNSPEC_QDSP6_Q6A2_combineii))]
  "TARGET_V2_FEATURES"
  "%P0=combine(#%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_combine_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_hh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_combine_hh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_hh))]
  ""
  "%0=combine(%1.h,%2.h)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_combine_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_hl))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_combine_hl"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_hl))]
  ""
  "%0=combine(%1.h,%2.l)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_combine_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_lh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_combine_lh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_lh))]
  ""
  "%0=combine(%1.l,%2.h)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_combine_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_ll))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_combine_ll"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_combine_ll))]
  ""
  "%0=combine(%1.l,%2.l)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_tfril"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "immediate_operand" "Iu16")
        ] UNSPEC_QDSP6_Q6A2_tfril))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_Rl_equals_I intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu16")){
      error("argument 2 of Q6_Rl_equals_I intrinsic cannot be encoded as u16 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_tfril"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "immediate_operand" "Iu16")
        ] UNSPEC_QDSP6_Q6A2_tfril))]
  ""
  "%0.l=#%2"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_tfrih"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "immediate_operand" "Iu16")
        ] UNSPEC_QDSP6_Q6A2_tfrih))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_Rh_equals_I intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu16")){
      error("argument 2 of Q6_Rh_equals_I intrinsic cannot be encoded as u16 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_tfrih"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "immediate_operand" "Iu16")
        ] UNSPEC_QDSP6_Q6A2_tfrih))]
  ""
  "%0.h=#%2"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_and))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_andsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_and_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_and))]
  "TARGET_V2_FEATURES"
  "%0=and(%1,%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_and_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_and))]
  "!TARGET_V2_FEATURES"
  "%0=and(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_or))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_iorsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_or_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_or))]
  "TARGET_V2_FEATURES"
  "%0=or(%1,%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_or_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_or))]
  "!TARGET_V2_FEATURES"
  "%0=or(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_xor"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_xor))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_xorsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_xor_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_xor))]
  "TARGET_V2_FEATURES"
  "%0=xor(%1,%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_xor_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_xor))]
  "!TARGET_V2_FEATURES"
  "%0=xor(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_not"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_not))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_one_cmplsi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_not_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_not))]
  "TARGET_V2_FEATURES"
  "%0=not(%1)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_not_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_not))]
  "!TARGET_V2_FEATURES"
  "%0=not(%1)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M2_xor_xacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_xor_xacc))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_xor_xacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_xor_xacc))]
  "TARGET_V2_FEATURES"
  "%0^=xor(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_xor_xacc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_xacc))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_xor_xacc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_xacc))]
  "TARGET_V4_FEATURES"
  "%P0^=xor(%P2,%P3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_andn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_andn))]
  "TARGET_V4_FEATURES"
  "%0=and(%1,~%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_orn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_orn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_orn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_orn))]
  "TARGET_V4_FEATURES"
  "%0=or(%1,~%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A4_andnp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_andnp))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_andnp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_andnp))]
  "TARGET_V4_FEATURES"
  "%P0=and(%P1,~%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_ornp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_ornp))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_ornp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_ornp))]
  "TARGET_V4_FEATURES"
  "%P0=or(%P1,~%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_addaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is6")
        ] UNSPEC_QDSP6_Q6S4_addaddi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_add_add_RRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is6")){
      error("argument 3 of Q6_R_add_add_RRI intrinsic cannot be encoded as s6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_addaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is6")
        ] UNSPEC_QDSP6_Q6S4_addaddi))]
  "TARGET_V4_FEATURES"
  "%0=add(%1,add(%2,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_subaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is6")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_subaddi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_add_sub_RIR intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is6")){
      error("argument 2 of Q6_R_add_sub_RIR intrinsic cannot be encoded as s6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_subaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is6")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_subaddi))]
  "TARGET_V4_FEATURES"
  "%0=add(%1,sub(#%2,%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M4_and_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_and))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_and_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_and))]
  "TARGET_V4_FEATURES"
  "%0&=and(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_and_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_andn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_and_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_andn))]
  "TARGET_V4_FEATURES"
  "%0&=and(%2,~%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_and_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_or))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_and_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_or))]
  "TARGET_V4_FEATURES"
  "%0&=or(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_and_xor"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_xor))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_and_xor"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_and_xor))]
  "TARGET_V4_FEATURES"
  "%0&=xor(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_or_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_and))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_or_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_and))]
  "TARGET_V4_FEATURES"
  "%0|=and(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_or_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_andn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_or_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_andn))]
  "TARGET_V4_FEATURES"
  "%0|=and(%2,~%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_or_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_or))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_or_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_or))]
  "TARGET_V4_FEATURES"
  "%0|=or(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_or_xor"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_xor))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_or_xor"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_or_xor))]
  "TARGET_V4_FEATURES"
  "%0|=xor(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6S4_or_andix"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6S4_or_andix))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_or_and_RRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is10")){
      error("argument 3 of Q6_R_or_and_RRI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_or_andix"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6S4_or_andix))]
  "TARGET_V4_FEATURES"
  "%0=or(%2,and(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_or_andi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6S4_or_andi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_andor_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is10")){
      error("argument 3 of Q6_R_andor_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_or_andi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6S4_or_andi))]
  "TARGET_V4_FEATURES"
  "%0|=and(%2,#%3)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_or_ori"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6S4_or_ori))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_oror_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Is10")){
      error("argument 3 of Q6_R_oror_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_or_ori"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6S4_or_ori))]
  "TARGET_V4_FEATURES"
  "%0|=or(%2,#%3)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6M4_xor_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_and))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_xor_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_and))]
  "TARGET_V4_FEATURES"
  "%0^=and(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_xor_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_or))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_xor_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_or))]
  "TARGET_V4_FEATURES"
  "%0^=or(%2,%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M4_xor_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_andn))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M4_xor_andn"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M4_xor_andn))]
  "TARGET_V4_FEATURES"
  "%0^=and(%2,~%3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_subri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Is10")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subri))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_sub_IR intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Is10")){
      error("argument 1 of Q6_R_sub_IR intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_subri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Is10")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_subri))]
  "TARGET_V2_FEATURES"
  "%0=sub(#%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_andir"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6A2_andir))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_and_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is10")){
      error("argument 2 of Q6_R_and_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_andir"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6A2_andir))]
  "TARGET_V2_FEATURES"
  "%0=and(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_orir"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6A2_orir))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_or_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is10")){
      error("argument 2 of Q6_R_or_RI intrinsic cannot be encoded as s10 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_orir"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is10")
        ] UNSPEC_QDSP6_Q6A2_orir))]
  "TARGET_V2_FEATURES"
  "%0=or(%1,#%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_andp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_andp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_anddi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_andp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_andp))]
  ""
  "%P0=and(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_orp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_orp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_iordi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_orp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_orp))]
  ""
  "%P0=or(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_xorp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_xorp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_xordi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_xorp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_xorp))]
  ""
  "%P0=xor(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_notp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_notp))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_one_cmpldi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_notp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_notp))]
  ""
  "%P0=not(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_sxtw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sxtw))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_extendsidi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6A2_sxtw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sxtw))]
  ""
  "%P0=sxtw(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sat))]
  ""
  "%0=sat(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_sath"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sath))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_sath"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_sath))]
  ""
  "%0=sath(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_satuh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_satuh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_satuh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_satuh))]
  ""
  "%0=satuh(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_satub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_satub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_satub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_satub))]
  ""
  "%0=satub(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_satb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_satb))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_satb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_satb))]
  "TARGET_V2_FEATURES"
  "%0=satb(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddub))]
  ""
  "%P0=vaddub(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddb_map"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddb_map))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddb_map"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddb_map))]
  "TARGET_V4_FEATURES"
  "%P0=vaddb(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddubs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddubs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddubs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddubs))]
  ""
  "%P0=vaddub(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddh))]
  ""
  "%P0=vaddh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddhs))]
  ""
  "%P0=vaddh(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vadduhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vadduhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vadduhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vadduhs))]
  ""
  "%P0=vadduh(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddw))]
  ""
  "%P0=vaddw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vaddws"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddws))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vaddws"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vaddws))]
  ""
  "%P0=vaddw(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_vxaddsubw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxaddsubw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vxaddsubw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxaddsubw))]
  "TARGET_V4_FEATURES"
  "%P0=vxaddsubw(%P1,%P2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vxsubaddw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxsubaddw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vxsubaddw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxsubaddw))]
  "TARGET_V4_FEATURES"
  "%P0=vxsubaddw(%P1,%P2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vxaddsubh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxaddsubh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vxaddsubh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxaddsubh))]
  "TARGET_V4_FEATURES"
  "%P0=vxaddsubh(%P1,%P2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vxsubaddh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxsubaddh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vxsubaddh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxsubaddh))]
  "TARGET_V4_FEATURES"
  "%P0=vxsubaddh(%P1,%P2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vxaddsubhr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxaddsubhr))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vxaddsubhr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxaddsubhr))]
  "TARGET_V4_FEATURES"
  "%P0=vxaddsubh(%P1,%P2):rnd:>>1:sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_vxsubaddhr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxsubaddhr))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_vxsubaddhr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_vxsubaddhr))]
  "TARGET_V4_FEATURES"
  "%P0=vxsubaddh(%P1,%P2):rnd:>>1:sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_svavgh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svavgh))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svavgh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svavgh))]
  "TARGET_V2_FEATURES"
  "%0=vavgh(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_svavghs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svavghs))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svavghs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svavghs))]
  "TARGET_V2_FEATURES"
  "%0=vavgh(%1,%2):rnd"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_svnavgh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svnavgh))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svnavgh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svnavgh))]
  "TARGET_V2_FEATURES"
  "%0=vnavgh(%1,%2)"
  [(set_attr "type" "A")]
)


(define_expand "qdsp6_builtin_Q6A2_svaddh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svaddh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svaddh_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svaddh))]
  "TARGET_V2_FEATURES"
  "%0=vaddh(%1,%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_svaddh_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svaddh))]
  "!TARGET_V2_FEATURES"
  "%0=vaddh(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_svaddhs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svaddhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svaddhs_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svaddhs))]
  "TARGET_V2_FEATURES"
  "%0=vaddh(%1,%2):sat"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_svaddhs_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svaddhs))]
  "!TARGET_V2_FEATURES"
  "%0=vaddh(%1,%2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_svadduhs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svadduhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svadduhs_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svadduhs))]
  "TARGET_V2_FEATURES"
  "%0=vadduh(%1,%2):sat"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_svadduhs_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svadduhs))]
  "!TARGET_V2_FEATURES"
  "%0=vadduh(%1,%2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_svsubh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svsubh_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubh))]
  "TARGET_V2_FEATURES"
  "%0=vsubh(%1,%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_svsubh_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubh))]
  "!TARGET_V2_FEATURES"
  "%0=vsubh(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_svsubhs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svsubhs_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubhs))]
  "TARGET_V2_FEATURES"
  "%0=vsubh(%1,%2):sat"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_svsubhs_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubhs))]
  "!TARGET_V2_FEATURES"
  "%0=vsubh(%1,%2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_svsubuhs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubuhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_svsubuhs_v2"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubuhs))]
  "TARGET_V2_FEATURES"
  "%0=vsubuh(%1,%2):sat"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6A2_svsubuhs_v1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_svsubuhs))]
  "!TARGET_V2_FEATURES"
  "%0=vsubuh(%1,%2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vraddub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vraddub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vraddub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vraddub))]
  ""
  "%P0=vraddub(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vraddub_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vraddub_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vraddub_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vraddub_acc))]
  ""
  "%P0+=vraddub(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vraddh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vraddh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vraddh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vraddh))]
  "TARGET_V4_FEATURES"
  "%0=vraddh(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vradduh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vradduh))]
  "TARGET_V3_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vradduh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vradduh))]
  "TARGET_V3_FEATURES"
  "%0=vradduh(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubub))]
  ""
  "%P0=vsubub(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubb_map"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubb_map))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubb_map"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubb_map))]
  "TARGET_V4_FEATURES"
  "%P0=vsubb(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vsububs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsububs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsububs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsububs))]
  ""
  "%P0=vsubub(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubh))]
  ""
  "%P0=vsubh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubhs))]
  ""
  "%P0=vsubh(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubuhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubuhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubuhs"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubuhs))]
  ""
  "%P0=vsubuh(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubw))]
  ""
  "%P0=vsubw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vsubws"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubws))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vsubws"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vsubws))]
  ""
  "%P0=vsubw(%P1,%P2):sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vabsh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabsh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vabsh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabsh))]
  ""
  "%P0=vabsh(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vabshsat"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabshsat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vabshsat"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabshsat))]
  ""
  "%P0=vabsh(%P1):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vabsw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabsw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vabsw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabsw))]
  ""
  "%P0=vabsw(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vabswsat"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabswsat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vabswsat"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vabswsat))]
  ""
  "%P0=vabsw(%P1):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6M2_vabsdiffw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vabsdiffw))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vabsdiffw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vabsdiffw))]
  "TARGET_V2_FEATURES"
  "%P0=vabsdiffw(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6M2_vabsdiffh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vabsdiffh))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6M2_vabsdiffh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6M2_vabsdiffh))]
  "TARGET_V2_FEATURES"
  "%P0=vabsdiffh(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vrsadub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vrsadub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vrsadub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vrsadub))]
  ""
  "%P0=vrsadub(%P1,%P2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vrsadub_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vrsadub_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vrsadub_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vrsadub_acc))]
  ""
  "%P0+=vrsadub(%P2,%P3)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A2_vavgub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavgub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgub))]
  ""
  "%P0=vavgub(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavguh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavguh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguh))]
  ""
  "%P0=vavguh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavgh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavgh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgh))]
  ""
  "%P0=vavgh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vnavgh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vnavgh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgh))]
  ""
  "%P0=vnavgh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavgw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavgw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgw))]
  ""
  "%P0=vavgw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vnavgw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgw))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vnavgw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgw))]
  "TARGET_V2_FEATURES"
  "%P0=vnavgw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavgwr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgwr))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavgwr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgwr))]
  ""
  "%P0=vavgw(%P1,%P2):rnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vnavgwr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgwr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vnavgwr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgwr))]
  "TARGET_V2_FEATURES"
  "%P0=vnavgw(%P1,%P2):rnd:sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavgwcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgwcr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavgwcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgwcr))]
  "TARGET_V2_FEATURES"
  "%P0=vavgw(%P1,%P2):crnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vnavgwcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgwcr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vnavgwcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavgwcr))]
  "TARGET_V2_FEATURES"
  "%P0=vnavgw(%P1,%P2):crnd:sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavghcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavghcr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavghcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavghcr))]
  "TARGET_V2_FEATURES"
  "%P0=vavgh(%P1,%P2):crnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vnavghcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavghcr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vnavghcr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavghcr))]
  "TARGET_V2_FEATURES"
  "%P0=vnavgh(%P1,%P2):crnd:sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavguw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavguw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguw))]
  ""
  "%P0=vavguw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavguwr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguwr))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavguwr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguwr))]
  ""
  "%P0=vavguw(%P1,%P2):rnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavgubr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgubr))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavgubr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavgubr))]
  ""
  "%P0=vavgub(%P1,%P2):rnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavguhr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguhr))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavguhr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavguhr))]
  ""
  "%P0=vavguh(%P1,%P2):rnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vavghr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavghr))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vavghr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vavghr))]
  ""
  "%P0=vavgh(%P1,%P2):rnd"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vnavghr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavghr))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vnavghr"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vnavghr))]
  "TARGET_V2_FEATURES"
  "%P0=vnavgh(%P1,%P2):rnd:sat"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_round_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_round_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_round_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_round_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_round_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_round_ri))]
  "TARGET_V4_FEATURES"
  "%0=round(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_round_rr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_round_rr))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_round_rr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_round_rr))]
  "TARGET_V4_FEATURES"
  "%0=round(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_round_ri_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_round_ri_sat))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_round_RI_sat intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_round_RI_sat intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_round_ri_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_round_ri_sat))]
  "TARGET_V4_FEATURES"
  "%0=round(%1,#%2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_round_rr_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_round_rr_sat))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_round_rr_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_round_rr_sat))]
  "TARGET_V4_FEATURES"
  "%0=round(%1,%2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cround_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_cround_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_cround_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_cround_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_cround_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_cround_ri))]
  "TARGET_V4_FEATURES"
  "%0=cround(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_cround_rr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cround_rr))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_cround_rr"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_cround_rr))]
  "TARGET_V4_FEATURES"
  "%0=cround(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrminh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrminh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminh))]
  "TARGET_V4_FEATURES"
  "%P0=vrminh(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrmaxh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrmaxh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxh))]
  "TARGET_V4_FEATURES"
  "%P0=vrmaxh(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrminuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminuh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrminuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminuh))]
  "TARGET_V4_FEATURES"
  "%P0=vrminuh(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrmaxuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxuh))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrmaxuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxuh))]
  "TARGET_V4_FEATURES"
  "%P0=vrmaxuh(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrminw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrminw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminw))]
  "TARGET_V4_FEATURES"
  "%P0=vrminw(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrmaxw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrmaxw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxw))]
  "TARGET_V4_FEATURES"
  "%P0=vrmaxw(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrminuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminuw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrminuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrminuw))]
  "TARGET_V4_FEATURES"
  "%P0=vrminuw(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_vrmaxuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxuw))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_vrmaxuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_vrmaxuw))]
  "TARGET_V4_FEATURES"
  "%P0=vrmaxuw(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A2_vminb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminb))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vminb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminb))]
  "TARGET_V4_FEATURES"
  "%P0=vminb(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vmaxb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxb))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vmaxb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxb))]
  "TARGET_V4_FEATURES"
  "%P0=vmaxb(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vminub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vminub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminub))]
  ""
  "%P0=vminub(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vmaxub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vmaxub"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxub))]
  ""
  "%P0=vmaxub(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vminh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vminh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminh))]
  ""
  "%P0=vminh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vmaxh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vmaxh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxh))]
  ""
  "%P0=vmaxh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vminuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminuh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vminuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminuh))]
  ""
  "%P0=vminuh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vmaxuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxuh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vmaxuh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxuh))]
  ""
  "%P0=vmaxuh(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vminw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vminw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminw))]
  ""
  "%P0=vminw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vmaxw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vmaxw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxw))]
  ""
  "%P0=vmaxw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vminuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminuw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vminuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vminuw))]
  ""
  "%P0=vminuw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_vmaxuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxuw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_vmaxuw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_vmaxuw))]
  ""
  "%P0=vmaxuw(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A4_modwrapu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_modwrapu))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_modwrapu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_modwrapu))]
  "TARGET_V4_FEATURES"
  "%0=modwrap(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r))]
  ""
  "%0=asr(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r))]
  ""
  "%0=asl(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r))]
  ""
  "%0=lsr(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r))]
  ""
  "%0=lsl(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p))]
  ""
  "%P0=asr(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p))]
  ""
  "%P0=asl(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p))]
  ""
  "%P0=lsr(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p))]
  ""
  "%P0=lsl(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_acc))]
  ""
  "%0+=asr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_acc))]
  ""
  "%0+=asl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_acc))]
  ""
  "%0+=lsr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_acc))]
  ""
  "%0+=lsl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_acc))]
  ""
  "%P0+=asr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_acc))]
  ""
  "%P0+=asl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_acc))]
  ""
  "%P0+=lsr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_acc))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_acc))]
  ""
  "%P0+=lsl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_nac))]
  ""
  "%0-=asr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_nac))]
  ""
  "%0-=asl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_nac))]
  ""
  "%0-=lsr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_nac))]
  ""
  "%0-=lsl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_nac))]
  ""
  "%P0-=asr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_nac))]
  ""
  "%P0-=asl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_nac))]
  ""
  "%P0-=lsr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_nac))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_nac))]
  ""
  "%P0-=lsl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_and))]
  ""
  "%0&=asr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_and))]
  ""
  "%0&=asl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_and))]
  ""
  "%0&=lsr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_and))]
  ""
  "%0&=lsl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_or))]
  ""
  "%0|=asr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_or))]
  ""
  "%0|=asl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_r_or))]
  ""
  "%0|=lsr(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_r_or))]
  ""
  "%0|=lsl(%2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_and))]
  ""
  "%P0&=asr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_and))]
  ""
  "%P0&=asl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_and))]
  ""
  "%P0&=lsr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_and))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_and))]
  ""
  "%P0&=lsl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_or))]
  ""
  "%P0|=asr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_or))]
  ""
  "%P0|=asl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_or))]
  ""
  "%P0|=lsr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_or))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_or))]
  ""
  "%P0|=lsl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_xor))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_p_xor))]
  "TARGET_V4_FEATURES"
  "%P0^=asr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_xor))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_p_xor))]
  "TARGET_V4_FEATURES"
  "%P0^=asl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_xor))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_p_xor))]
  "TARGET_V4_FEATURES"
  "%P0^=lsr(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_xor))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_p_xor"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_p_xor))]
  "TARGET_V4_FEATURES"
  "%P0^=lsl(%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_r_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_sat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_r_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_r_sat))]
  ""
  "%0=asr(%1,%2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_r_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_sat))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_r_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_r_sat))]
  ""
  "%0=asl(%1,%2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_asr_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_asr_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r))]
  ""
  "%0=asr(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_lsr_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_lsr_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r))]
  ""
  "%0=lsr(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_asl_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_asl_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r))]
  ""
  "%0=asl(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_asr_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_P_asr_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrdi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p))]
  ""
  "%P0=asr(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_lsr_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_P_lsr_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrdi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p))]
  ""
  "%P0=lsr(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_asl_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_P_asl_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashldi3(operands[0], operands[1], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_p"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p))]
  ""
  "%P0=asl(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_acc))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_asracc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_asracc_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3_acc(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_acc))]
  ""
  "%0+=asr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_acc))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_lsracc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_lsracc_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrsi3_acc(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_acc))]
  ""
  "%0+=lsr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_acc))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_aslacc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_aslacc_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3_acc(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r_acc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_acc))]
  ""
  "%0+=asl(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_acc))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_asracc_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_asracc_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrdi3_acc(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_acc))]
  ""
  "%P0+=asr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_acc))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_lsracc_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_lsracc_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrdi3_acc(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_acc))]
  ""
  "%P0+=lsr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_acc))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_aslacc_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_aslacc_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashldi3_acc(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_p_acc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_acc))]
  ""
  "%P0+=asl(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_nac))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_asrnac_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_asrnac_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3_nacc(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_nac))]
  ""
  "%0-=asr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_nac))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_lsrnac_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_lsrnac_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrsi3_nacc(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_nac))]
  ""
  "%0-=lsr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_nac))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_aslnac_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_aslnac_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3_nacc(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r_nac"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_nac))]
  ""
  "%0-=asl(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_nac))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_asrnac_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_asrnac_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrdi3_nacc(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_nac))]
  ""
  "%P0-=asr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_nac))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_lsrnac_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_lsrnac_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrdi3_nacc(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_nac))]
  ""
  "%P0-=lsr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_nac))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_aslnac_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_aslnac_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashldi3_nacc(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_p_nac"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_nac))]
  ""
  "%P0-=asl(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_r_xacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_xacc))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_lsrxacc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_lsrxacc_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrsi3_xor(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_r_xacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_xacc))]
  "TARGET_V2_FEATURES"
  "%0^=lsr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r_xacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_xacc))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_aslxacc_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_aslxacc_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3_xor(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r_xacc"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_xacc))]
  "TARGET_V2_FEATURES"
  "%0^=asl(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_p_xacc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_xacc))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_lsrxacc_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_lsrxacc_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrdi3_xor(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_p_xacc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_xacc))]
  "TARGET_V2_FEATURES"
  "%P0^=lsr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_p_xacc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_xacc))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_aslxacc_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_aslxacc_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashldi3_xor(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_p_xacc"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_xacc))]
  "TARGET_V2_FEATURES"
  "%P0^=asl(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_and))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_asrand_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_asrand_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3_and(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_and))]
  ""
  "%0&=asr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_and))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_lsrand_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_lsrand_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrsi3_and(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_and))]
  ""
  "%0&=lsr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_and))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_asland_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_asland_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3_and(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r_and"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_and))]
  ""
  "%0&=asl(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_or))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_asror_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_asror_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3_or(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_or))]
  ""
  "%0|=asr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_or))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_lsror_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_lsror_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrsi3_or(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_r_or))]
  ""
  "%0|=lsr(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_or))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_aslor_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_aslor_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashlsi3_or(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r_or"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_or))]
  ""
  "%0|=asl(%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_and))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_asrand_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_asrand_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrdi3_and(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_and))]
  ""
  "%P0&=asr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_and))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_lsrand_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_lsrand_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrdi3_and(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_and))]
  ""
  "%P0&=lsr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_and))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_asland_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_asland_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashldi3_and(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_p_and"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_and))]
  ""
  "%P0&=asl(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_or))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_asror_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_asror_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrdi3_or(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asr_i_p_or))]
  ""
  "%P0|=asr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_or))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_lsror_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_lsror_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_lshrdi3_or(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_p_or))]
  ""
  "%P0|=lsr(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_or))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_aslor_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_aslor_PI intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashldi3_or(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_p_or"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_asl_i_p_or))]
  ""
  "%P0|=asl(%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_r_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_sat))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_asl_RI_sat intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_asl_RI_sat intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_r_sat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_r_sat))]
  ""
  "%0=asl(%1,#%2):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r_rnd"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_rnd))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_asr_RI_rnd intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_asr_RI_rnd intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r_rnd"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_rnd))]
  ""
  "%0=asr(%1,#%2):rnd"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_r_rnd_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_rnd_goodsyntax))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_asrrnd_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_asrrnd_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_r_rnd_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_r_rnd_goodsyntax))]
  "TARGET_V2_FEATURES"
  "%0=asrrnd(%1,#%2)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6S4_lsli"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Is6")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_lsli))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_lsl_IR intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Is6")){
      error("argument 1 of Q6_R_lsl_IR intrinsic cannot be encoded as s6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_lsli"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Is6")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_lsli))]
  "TARGET_V4_FEATURES"
  "%0=lsl(#%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_addasl_rrri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu3")
        ] UNSPEC_QDSP6_Q6S2_addasl_rrri))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_addasl_RRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu3")){
      error("argument 3 of Q6_R_addasl_RRI intrinsic cannot be encoded as u3 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_addaslsi4(operands[0], operands[2], operands[3], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_addasl_rrri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu3")
        ] UNSPEC_QDSP6_Q6S2_addasl_rrri))]
  ""
  "%0=addasl(%1,%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_andi_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_andi_asl_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_and_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_and_asl_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_and_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_and_asl_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_andi_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_andi_asl_ri))]
  "TARGET_V4_FEATURES"
  "%0=and(#%2,asl(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_ori_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_ori_asl_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_or_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_or_asl_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_or_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_or_asl_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_ori_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_ori_asl_ri))]
  "TARGET_V4_FEATURES"
  "%0=or(#%2,asl(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_addi_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_addi_asl_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_add_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_add_asl_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_add_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_add_asl_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_addi_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_addi_asl_ri))]
  "TARGET_V4_FEATURES"
  "%0=add(#%2,asl(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_subi_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_subi_asl_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_sub_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_sub_asl_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_sub_asl_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_sub_asl_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_subi_asl_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_subi_asl_ri))]
  "TARGET_V4_FEATURES"
  "%0=sub(#%2,asl(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_andi_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_andi_lsr_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_and_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_and_lsr_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_and_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_and_lsr_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_andi_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_andi_lsr_ri))]
  "TARGET_V4_FEATURES"
  "%0=and(#%2,lsr(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_ori_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_ori_lsr_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_or_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_or_lsr_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_or_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_or_lsr_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_ori_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_ori_lsr_ri))]
  "TARGET_V4_FEATURES"
  "%0=or(#%2,lsr(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_addi_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_addi_lsr_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_add_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_add_lsr_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_add_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_add_lsr_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_addi_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_addi_lsr_ri))]
  "TARGET_V4_FEATURES"
  "%0=add(#%2,lsr(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_subi_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_subi_lsr_ri))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[1]) != CONST_INT){
      error("non-constant integer passed to argument 1 of Q6_R_sub_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[1]), 'I', "Iu8")){
      error("argument 1 of Q6_R_sub_lsr_IRI intrinsic cannot be encoded as u8 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_sub_lsr_IRI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_sub_lsr_IRI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_subi_lsr_ri"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "immediate_operand" "Iu8")
          (match_operand:SI 2 "gr_register_operand" "0")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_subi_lsr_ri))]
  "TARGET_V4_FEATURES"
  "%0=sub(#%2,lsr(%0,#%3))"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S2_valignib"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu3")
        ] UNSPEC_QDSP6_Q6S2_valignib))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_valignb_PPI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu3")){
      error("argument 3 of Q6_P_valignb_PPI intrinsic cannot be encoded as u3 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_valignib"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu3")
        ] UNSPEC_QDSP6_Q6S2_valignib))]
  ""
  "%P0=valignb(%P1,%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_valignrb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6S2_valignrb))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_valignrb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6S2_valignrb))]
  ""
  "%P0=valignb(%P1,%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vspliceib"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu3")
        ] UNSPEC_QDSP6_Q6S2_vspliceib))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_vspliceb_PPI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu3")){
      error("argument 3 of Q6_P_vspliceb_PPI intrinsic cannot be encoded as u3 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_vspliceib"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu3")
        ] UNSPEC_QDSP6_Q6S2_vspliceib))]
  ""
  "%P0=vspliceb(%P1,%P2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsplicerb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6S2_vsplicerb))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsplicerb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:QI 3 "pr_register_operand" "Rp")
        ] UNSPEC_QDSP6_Q6S2_vsplicerb))]
  ""
  "%P0=vspliceb(%P1,%P2,%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsplatrh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsplatrh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsplatrh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsplatrh))]
  ""
  "%P0=vsplath(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsplatrb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsplatrb))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsplatrb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsplatrb))]
  ""
  "%0=vsplatb(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_insert"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_insert))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_insert_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_insert_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[4]) != CONST_INT){
      error("non-constant integer passed to argument 4 of Q6_R_insert_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[4]), 'I', "Iu5")){
      error("argument 4 of Q6_R_insert_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_move_insn(operands[0], operands[1]);
      emit_insn(gen_insv(operands[0], operands[3], operands[4], operands[2]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_insert"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu5")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_insert))]
  ""
  "%0=insert(%2,#%3,#%4)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_tableidxb_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxb_goodsyntax))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_tableidxb_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu4")){
      error("argument 3 of Q6_R_tableidxb_RII intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[4]) != CONST_INT){
      error("non-constant integer passed to argument 4 of Q6_R_tableidxb_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[4]), 'I', "Iu5")){
      error("argument 4 of Q6_R_tableidxb_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_tableidxb_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxb_goodsyntax))]
  "TARGET_V2_FEATURES"
  "%0=tableidxb(%2,#%3,#%4)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6S2_tableidxh_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxh_goodsyntax))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_tableidxh_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu4")){
      error("argument 3 of Q6_R_tableidxh_RII intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[4]) != CONST_INT){
      error("non-constant integer passed to argument 4 of Q6_R_tableidxh_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[4]), 'I', "Iu5")){
      error("argument 4 of Q6_R_tableidxh_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_tableidxh_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxh_goodsyntax))]
  "TARGET_V2_FEATURES"
  "%0=tableidxh(%2,#%3,#%4)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6S2_tableidxw_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxw_goodsyntax))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_tableidxw_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu4")){
      error("argument 3 of Q6_R_tableidxw_RII intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[4]) != CONST_INT){
      error("non-constant integer passed to argument 4 of Q6_R_tableidxw_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[4]), 'I', "Iu5")){
      error("argument 4 of Q6_R_tableidxw_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_tableidxw_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxw_goodsyntax))]
  "TARGET_V2_FEATURES"
  "%0=tableidxw(%2,#%3,#%4)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6S2_tableidxd_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxd_goodsyntax))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_tableidxd_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu4")){
      error("argument 3 of Q6_R_tableidxd_RII intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[4]) != CONST_INT){
      error("non-constant integer passed to argument 4 of Q6_R_tableidxd_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[4]), 'I', "Iu5")){
      error("argument 4 of Q6_R_tableidxd_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_tableidxd_goodsyntax"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu4")
          (match_operand:SI 4 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tableidxd_goodsyntax))]
  "TARGET_V2_FEATURES"
  "%0=tableidxd(%2,#%3,#%4)"
  [(set_attr "type" "M")]
)


(define_expand "qdsp6_builtin_Q6A4_bitspliti"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_bitspliti))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_bitsplit_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_P_bitsplit_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6A4_bitspliti"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6A4_bitspliti))]
  "TARGET_V4_FEATURES"
  "%P0=bitsplit(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6A4_bitsplit"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_bitsplit))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A4_bitsplit"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A4_bitsplit))]
  "TARGET_V4_FEATURES"
  "%P0=bitsplit(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S4_extract"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_extract))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_extract_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_extract_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_extract_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_extract_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_extract"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_extract))]
  "TARGET_V4_FEATURES"
  "%0=extract(%1,#%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_extractu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_extractu))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_extractu_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_extractu_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_R_extractu_RII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu5")){
      error("argument 3 of Q6_R_extractu_RII intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_extzv(operands[0], operands[1], operands[2], operands[3]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_extractu"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
          (match_operand:SI 3 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_extractu))]
  ""
  "%0=extractu(%1,#%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_insertp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
          (match_operand:SI 4 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_insertp))]
  ""
  {
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_insert_PII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_insert_PII intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[4]) != CONST_INT){
      error("non-constant integer passed to argument 4 of Q6_P_insert_PII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[4]), 'I', "Iu6")){
      error("argument 4 of Q6_P_insert_PII intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_insertp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:SI 3 "immediate_operand" "Iu6")
          (match_operand:SI 4 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_insertp))]
  ""
  "%P0=insert(%P2,#%3,#%4)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_extractp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S4_extractp))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_extract_PII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_P_extract_PII intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_extract_PII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_extract_PII intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_extractp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S4_extractp))]
  "TARGET_V4_FEATURES"
  "%P0=extract(%P1,#%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_extractup"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_extractup))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_extractu_PII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu6")){
      error("argument 2 of Q6_P_extractu_PII intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
    if(GET_CODE (operands[3]) != CONST_INT){
      error("non-constant integer passed to argument 3 of Q6_P_extractu_PII intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[3]), 'I', "Iu6")){
      error("argument 3 of Q6_P_extractu_PII intrinsic cannot be encoded as u6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_extractup"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu6")
          (match_operand:SI 3 "immediate_operand" "Iu6")
        ] UNSPEC_QDSP6_Q6S2_extractup))]
  ""
  "%P0=extractu(%P1,#%2,#%3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_insert_rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_insert_rp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_insert_rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "0")
          (match_operand:SI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_insert_rp))]
  ""
  "%0=insert(%2,%P3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_extract_rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_extract_rp))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_extract_rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_extract_rp))]
  "TARGET_V4_FEATURES"
  "%0=extract(%1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_extractu_rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_extractu_rp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_extractu_rp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_extractu_rp))]
  ""
  "%0=extractu(%1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_insertp_rp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_insertp_rp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_insertp_rp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "0")
          (match_operand:DI 2 "gr_register_operand" "Rg")
          (match_operand:DI 3 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_insertp_rp))]
  ""
  "%P0=insert(%P2,%P3)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_extractp_rp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_extractp_rp))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_extractp_rp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_extractp_rp))]
  "TARGET_V4_FEATURES"
  "%P0=extract(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_extractup_rp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_extractup_rp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_extractup_rp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_extractup_rp))]
  ""
  "%P0=extractu(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_tstbit_i"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tstbit_i))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_tstbit_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_p_tstbit_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_tstbit_i"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_tstbit_i))]
  ""
  "%0=tstbit(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_ntstbit_i"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_ntstbit_i))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_p_tstbit_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_p_tstbit_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_ntstbit_i"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S4_ntstbit_i))]
  "TARGET_V4_FEATURES"
  "%0=!tstbit(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_setbit_i"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_setbit_i))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_setbit_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_setbit_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_setbitsi(operands[0], operands[2], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_setbit_i"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_setbit_i))]
  ""
  "%0=setbit(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_togglebit_i"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_togglebit_i))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_togglebit_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_togglebit_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_togglebitsi(operands[0], operands[2], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_togglebit_i"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_togglebit_i))]
  ""
  "%0=togglebit(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_clrbit_i"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_clrbit_i))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_clrbit_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_clrbit_RI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_clrbitsi(operands[0], operands[2], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_clrbit_i"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_clrbit_i))]
  ""
  "%0=clrbit(%1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_tstbit_r"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_tstbit_r))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_tstbit_r"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_tstbit_r))]
  ""
  "%0=tstbit(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_ntstbit_r"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_ntstbit_r))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_ntstbit_r"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_ntstbit_r))]
  "TARGET_V4_FEATURES"
  "%0=!tstbit(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_setbit_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_setbit_r))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_setbitsi(operands[0], operands[2], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_setbit_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_setbit_r))]
  ""
  "%0=setbit(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_togglebit_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_togglebit_r))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_togglebitsi(operands[0], operands[2], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_togglebit_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_togglebit_r))]
  ""
  "%0=togglebit(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_clrbit_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clrbit_r))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_clrbitsi(operands[0], operands[2], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_clrbit_r"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clrbit_r))]
  ""
  "%0=clrbit(%1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu4")
        ] UNSPEC_QDSP6_Q6S2_asr_i_vh))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_vasrh_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu4")){
      error("argument 2 of Q6_P_vasrh_PI intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu4")
        ] UNSPEC_QDSP6_Q6S2_asr_i_vh))]
  ""
  "%P0=vasrh(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu4")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_vh))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_vlsrh_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu4")){
      error("argument 2 of Q6_P_vlsrh_PI intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu4")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_vh))]
  ""
  "%P0=vlsrh(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu4")
        ] UNSPEC_QDSP6_Q6S2_asl_i_vh))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_vaslh_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu4")){
      error("argument 2 of Q6_P_vaslh_PI intrinsic cannot be encoded as u4 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu4")
        ] UNSPEC_QDSP6_Q6S2_asl_i_vh))]
  ""
  "%P0=vaslh(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_vh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_vh))]
  ""
  "%P0=vasrh(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_vh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_vh))]
  ""
  "%P0=vaslh(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_vh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_vh))]
  ""
  "%P0=vlsrh(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_vh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_vh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_vh))]
  ""
  "%P0=vlslh(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_vw))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_vasrw_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_P_vasrw_PI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_vw))]
  ""
  "%P0=vasrw(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_i_svw_trun"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_svw_trun))]
  "TARGET_V2_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_vasrw_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_R_vasrw_PI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_i_svw_trun"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asr_i_svw_trun))]
  "TARGET_V2_FEATURES"
  "%0=vasrw(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_svw_trun"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_svw_trun))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_svw_trun"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_svw_trun))]
  "TARGET_V2_FEATURES"
  "%0=vasrw(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_i_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_vw))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_vlsrw_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_P_vlsrw_PI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_i_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_lsr_i_vw))]
  ""
  "%P0=vlsrw(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_i_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_vw))]
  ""
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_P_vaslw_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Iu5")){
      error("argument 2 of Q6_P_vaslw_PI intrinsic cannot be encoded as u5 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_i_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Iu5")
        ] UNSPEC_QDSP6_Q6S2_asl_i_vw))]
  ""
  "%P0=vaslw(%P1,#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asr_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_vw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asr_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asr_r_vw))]
  ""
  "%P0=vasrw(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_asl_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_vw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_asl_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_asl_r_vw))]
  ""
  "%P0=vaslw(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsr_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_vw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsr_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsr_r_vw))]
  ""
  "%P0=vlsrw(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_lsl_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_vw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lsl_r_vw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lsl_r_vw))]
  ""
  "%P0=vlslw(%P1,%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vrndpackwh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vrndpackwh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vrndpackwh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vrndpackwh))]
  ""
  "%0=vrndwh(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vrndpackwhs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vrndpackwhs))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vrndpackwhs"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vrndpackwhs))]
  ""
  "%0=vrndwh(%P1):sat"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsxtbh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsxtbh))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsxtbh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsxtbh))]
  "TARGET_V2_FEATURES"
  "%P0=vsxtbh(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vzxtbh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vzxtbh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vzxtbh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vzxtbh))]
  ""
  "%P0=vzxtbh(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsathub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathub))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsathub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathub))]
  ""
  "%0=vsathub(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_svsathub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_svsathub))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_svsathub"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_svsathub))]
  "TARGET_V2_FEATURES"
  "%0=vsathub(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_svsathb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_svsathb))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_svsathb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_svsathb))]
  "TARGET_V2_FEATURES"
  "%0=vsathb(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsathb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathb))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsathb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathb))]
  "TARGET_V2_FEATURES"
  "%0=vsathb(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vtrunohb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunohb))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vtrunohb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunohb))]
  "TARGET_V2_FEATURES"
  "%0=vtrunohb(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vtrunewh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunewh))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vtrunewh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunewh))]
  "TARGET_V2_FEATURES"
  "%P0=vtrunewh(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vtrunowh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunowh))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vtrunowh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunowh))]
  "TARGET_V2_FEATURES"
  "%P0=vtrunowh(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vtrunehb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunehb))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vtrunehb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vtrunehb))]
  ""
  "%0=vtrunehb(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsxthw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsxthw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsxthw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsxthw))]
  ""
  "%P0=vsxthw(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vzxthw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vzxthw))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vzxthw"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vzxthw))]
  ""
  "%P0=vzxthw(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsatwh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsatwh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwh))]
  ""
  "%0=vsatwh(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsatwuh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwuh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsatwuh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwuh))]
  ""
  "%0=vsatwuh(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_packhl"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_packhl))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_packhl_v4"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_packhl))]
  "TARGET_V4_FEATURES"
  "%P0=packhl(%1,%2)"
  [(set_attr "type" "A")]
)


(define_insn "qdsp6_unspec_Q6S2_packhl_v1"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_packhl))]
  "!TARGET_V4_FEATURES"
  "%P0=packhl(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6A2_swiz"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_swiz))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6A2_swiz"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6A2_swiz))]
  "TARGET_V2_FEATURES"
  "%0=swiz(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsathub_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathub_nopack))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsathub_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathub_nopack))]
  ""
  "%P0=vsathub(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsathb_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathb_nopack))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsathb_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsathb_nopack))]
  "TARGET_V2_FEATURES"
  "%P0=vsathb(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsatwh_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwh_nopack))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsatwh_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwh_nopack))]
  ""
  "%P0=vsatwh(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_vsatwuh_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwuh_nopack))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_vsatwuh_nopack"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_vsatwuh_nopack))]
  ""
  "%P0=vsatwuh(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_shuffob"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffob))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_shuffob"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffob))]
  ""
  "%P0=shuffob(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_shuffeb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffeb))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_shuffeb"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffeb))]
  ""
  "%P0=shuffeb(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_shuffoh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffoh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_shuffoh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffoh))]
  ""
  "%P0=shuffoh(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_shuffeh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffeh))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_shuffeh"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_shuffeh))]
  ""
  "%P0=shuffeh(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_parity"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_parity))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_parity"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_parity))]
  "TARGET_V4_FEATURES"
  "%0=parity(%1,%2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S2_parityp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_parityp))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_parityp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_parityp))]
  "TARGET_V2_FEATURES"
  "%0=parity(%P1,%P2)"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6S2_lfsp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lfsp))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_lfsp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:DI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_lfsp))]
  "TARGET_V2_FEATURES"
  "%P0=lfs(%P1,%P2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_clbnorm"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clbnorm))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_clbnorm"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clbnorm))]
  "TARGET_V2_FEATURES"
  "%0=normamt(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_clbaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is6")
        ] UNSPEC_QDSP6_Q6S4_clbaddi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_add_clb_RI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is6")){
      error("argument 2 of Q6_R_add_clb_RI intrinsic cannot be encoded as s6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_clbaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is6")
        ] UNSPEC_QDSP6_Q6S4_clbaddi))]
  "TARGET_V4_FEATURES"
  "%0=add(clb(%1),#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_clbpnorm"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_clbpnorm))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S4_clbpnorm"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S4_clbpnorm))]
  "TARGET_V4_FEATURES"
  "%0=normamt(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S4_clbpaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is6")
        ] UNSPEC_QDSP6_Q6S4_clbpaddi))]
  "TARGET_V4_FEATURES"
  {
    if(GET_CODE (operands[2]) != CONST_INT){
      error("non-constant integer passed to argument 2 of Q6_R_add_clb_PI intrinsic");
    }
    if(!CONST_OK_FOR_CONSTRAINT_P (INTVAL (operands[2]), 'I', "Is6")){
      error("argument 2 of Q6_R_add_clb_PI intrinsic cannot be encoded as s6 immediate -- FIXME: can it be extended?");
    }
  }
)


(define_insn "qdsp6_unspec_Q6S4_clbpaddi"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "immediate_operand" "Is6")
        ] UNSPEC_QDSP6_Q6S4_clbpaddi))]
  "TARGET_V4_FEATURES"
  "%0=add(clb(%P1),#%2)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_clb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clb))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_clb"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clb))]
  ""
  "%0=clb(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_cl0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl0))]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_clzsi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_cl0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl0))]
  ""
  "%0=cl0(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_cl1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl1))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_cl1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl1))]
  ""
  "%0=cl1(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_clbp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clbp))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_clbp"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_clbp))]
  ""
  "%0=clb(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_cl0p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl0p))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_cl0p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl0p))]
  ""
  "%0=cl0(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_cl1p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl1p))]
  ""
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_cl1p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_cl1p))]
  ""
  "%0=cl1(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_brev"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_brev))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_brev"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_brev))]
  "TARGET_V2_FEATURES"
  "%0=brev(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_brevp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_brevp))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_brevp"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_brevp))]
  "TARGET_V4_FEATURES"
  "%P0=brev(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_ct0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct0))]
  "TARGET_V2_FEATURES"
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ctzsi2(operands[0], operands[1]));
      DONE;
    }
  }
)


(define_insn "qdsp6_unspec_Q6S2_ct0"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct0))]
  "TARGET_V2_FEATURES"
  "%0=ct0(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_ct1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct1))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_ct1"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct1))]
  "TARGET_V2_FEATURES"
  "%0=ct1(%1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_ct0p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct0p))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_ct0p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct0p))]
  "TARGET_V4_FEATURES"
  "%0=ct0(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_ct1p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct1p))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_ct1p"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_ct1p))]
  "TARGET_V4_FEATURES"
  "%0=ct1(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_interleave"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_interleave))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_interleave"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_interleave))]
  "TARGET_V2_FEATURES"
  "%P0=interleave(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6S2_deinterleave"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_deinterleave))]
  "TARGET_V2_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6S2_deinterleave"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:DI 1 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6S2_deinterleave))]
  "TARGET_V2_FEATURES"
  "%P0=deinterleave(%P1)"
  [(set_attr "type" "S")]
)


(define_expand "qdsp6_builtin_Q6dep_S2_packhl"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6dep_S2_packhl))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6dep_S2_packhl"
  [(set (match_operand:DI 0 "gr_register_operand" "=Rg")
        (unspec:DI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6dep_S2_packhl))]
  "TARGET_V4_FEATURES"
  "%P0=packhl(%1,%2):deprecated"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6dep_A2_addsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6dep_A2_addsat))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6dep_A2_addsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6dep_A2_addsat))]
  "TARGET_V4_FEATURES"
  "%0=add(%1,%2):sat:deprecated"
  [(set_attr "type" "X")]
)


(define_expand "qdsp6_builtin_Q6dep_A2_subsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6dep_A2_subsat))]
  "TARGET_V4_FEATURES"
  {
  }
)


(define_insn "qdsp6_unspec_Q6dep_A2_subsat"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (unspec:SI [
          (match_operand:SI 1 "gr_register_operand" "Rg")
          (match_operand:SI 2 "gr_register_operand" "Rg")
        ] UNSPEC_QDSP6_Q6dep_A2_subsat))]
  "TARGET_V4_FEATURES"
  "%0=sub(%1,%2):sat:deprecated"
  [(set_attr "type" "X")]
)
