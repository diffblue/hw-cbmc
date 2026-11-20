# Cell libraries of the ground-truth flow, sourced by gt_flow.sh inside the
# openroad/orfs image. For every platform: the liberty files (typical
# corner; .gz is allowed), the technology and cell LEF files, and the
# cells synthesis must not use, as in the platform's config.mk in
# OpenROAD-flow-scripts. Where a platform offers several threshold
# voltages or track heights, one is chosen (the platform's default).

PLATFORMS=/OpenROAD-flow-scripts/flow/platforms

case "${PLATFORM:-nangate45}" in
nangate45)
  D=$PLATFORMS/nangate45
  LIBS="$D/lib/NangateOpenCellLibrary_typical.lib"
  LEFS="$D/lef/NangateOpenCellLibrary.tech.lef
        $D/lef/NangateOpenCellLibrary.macro.lef"
  DONT_USE="TAPCELL_X1 FILLCELL_X1"
  ;;
sky130hd)
  D=$PLATFORMS/sky130hd
  LIBS="$D/lib/sky130_fd_sc_hd__tt_025C_1v80.lib"
  LEFS="$D/lef/sky130_fd_sc_hd.tlef $D/lef/sky130_fd_sc_hd_merged.lef"
  DONT_USE="*probe* *lpflow* *macro_sparecell* *conb* *dlygate* *dlymetal*
            *clkdlybuf* *tapvpwrvgnd* *fill* *decap* *diode*"
  ;;
gf180)
  D=$PLATFORMS/gf180
  LIBS="$D/lib/gf180mcu_fd_sc_mcu9t5v0__tt_025C_5v00.lib.gz"
  LEFS="$D/lef/gf180mcu_5LM_1TM_9K_9t_tech.lef
        $D/lef/gf180mcu_5LM_1TM_9K_9t_sc.lef"
  DONT_USE="*_1 *fill* *endcap* *filltie* *antenna*"
  ;;
ihp-sg13g2)
  D=$PLATFORMS/ihp-sg13g2
  LIBS="$D/lib/sg13g2_stdcell_typ_1p20V_25C.lib"
  LEFS="$D/lef/sg13g2_tech.lef $D/lef/sg13g2_stdcell.lef"
  DONT_USE="sg13g2_lgcp_1 sg13g2_sighold sg13g2_slgcp_1 sg13g2_dfrbp_2
            *fill* *decap* *antennanp*"
  ;;
asap7)
  D=$PLATFORMS/asap7
  LIBS="$D/lib/NLDM/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib.gz
        $D/lib/NLDM/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib.gz
        $D/lib/NLDM/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib.gz
        $D/lib/NLDM/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib.gz
        $D/lib/NLDM/asap7sc7p5t_SEQ_RVT_TT_nldm_220123.lib"
  LEFS="$D/lef/asap7_tech_1x_201209.lef
        $D/lef/asap7sc7p5t_28_R_1x_220121a.lef"
  DONT_USE="*x1p*_ASAP7* *xp*_ASAP7* SDF* ICG* *TAPCELL* *FILLER* *DECAP*"
  ;;
gt2n)
  D=$PLATFORMS/gt2n
  LIBS="$D/lib/gt2_6t_w31_lvt_tt_0p7v25c.lib"
  LEFS="$D/lef/gt2_tech.lef $D/lef/gt2_6t_w31_lvt.lef"
  DONT_USE="*filler* *tapfspdn* *tapbspdn* *decapcc* *tiehigh* *tielow*"
  ;;
*)
  echo "unknown platform $PLATFORM" >&2
  exit 1
  ;;
esac
