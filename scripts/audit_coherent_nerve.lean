import SerrePositivity.InfinityCategories.Coherent
/-!
# Coherent nerve の公理監査

概要：γ1 の実装済みの明示的な公開宣言の公理と完全な型を表示する。
方針：全宣言を公理表示と #check @ で個別に検査する。
規約：許される公理は propext、Classical.choice、Quot.sound のみ。
使われ方：対象と集約をビルド後、lake env lean scripts/audit_coherent_nerve.lean。
原典：HTT 1.1.5.10、Kerodon 2.4.3–2.4.5。γ1 全体は未完了。
-/

set_option pp.universes true
set_option pp.explicit true






#print axioms SerrePositivity.InfinityCategories.Coherent.cube
#check @SerrePositivity.InfinityCategories.Coherent.cube

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeCoordinate
#check @SerrePositivity.InfinityCategories.Coherent.cubeCoordinate

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeCoordinateFunctor
#check @SerrePositivity.InfinityCategories.Coherent.cubeCoordinateFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeCoordinateMap
#check @SerrePositivity.InfinityCategories.Coherent.cubeCoordinateMap

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeRestFunctor
#check @SerrePositivity.InfinityCategories.Coherent.cubeRestFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeCoordinateMap_apply
#check @SerrePositivity.InfinityCategories.Coherent.cubeCoordinateMap_apply

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeCombineSimplex
#check @SerrePositivity.InfinityCategories.Coherent.cubeCombineSimplex

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeSplit
#check @SerrePositivity.InfinityCategories.Coherent.cubeSplit

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeUnsplit
#check @SerrePositivity.InfinityCategories.Coherent.cubeUnsplit

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeSplit_comp_cubeUnsplit
#check @SerrePositivity.InfinityCategories.Coherent.cubeSplit_comp_cubeUnsplit

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeUnsplit_comp_cubeSplit
#check @SerrePositivity.InfinityCategories.Coherent.cubeUnsplit_comp_cubeSplit

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeSplitIso
#check @SerrePositivity.InfinityCategories.Coherent.cubeSplitIso

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomViaFace
#check @SerrePositivity.InfinityCategories.Coherent.hornHomViaFace

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomViaFace_heq
#check @SerrePositivity.InfinityCategories.Coherent.hornHomViaFace_heq

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomViaFace_on_face
#check @SerrePositivity.InfinityCategories.Coherent.hornHomViaFace_on_face

#print axioms SerrePositivity.InfinityCategories.Coherent.hornZeroFaceHom
#check @SerrePositivity.InfinityCategories.Coherent.hornZeroFaceHom

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomViaFace_restrict
#check @SerrePositivity.InfinityCategories.Coherent.hornHomViaFace_restrict

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_factor
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_factor

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_point
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_point

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_succAbove
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_succAbove

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_section
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_section

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_spec
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_spec

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_image
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_image

#print axioms SerrePositivity.InfinityCategories.Coherent.faceRetraction_ulift_image
#check @SerrePositivity.InfinityCategories.Coherent.faceRetraction_ulift_image

#print axioms SerrePositivity.InfinityCategories.Coherent.thickening_faceRetraction_section
#check @SerrePositivity.InfinityCategories.Coherent.thickening_faceRetraction_section

#print axioms SerrePositivity.InfinityCategories.Coherent.mem_upperEndpoint_iff
#check @SerrePositivity.InfinityCategories.Coherent.mem_upperEndpoint_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.cubeBoundary
#check @SerrePositivity.InfinityCategories.Coherent.cubeBoundary

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCube
#check @SerrePositivity.InfinityCategories.Coherent.hollowCube

#print axioms SerrePositivity.InfinityCategories.Coherent.mem_hollowCube_iff
#check @SerrePositivity.InfinityCategories.Coherent.mem_hollowCube_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCubeIso
#check @SerrePositivity.InfinityCategories.Coherent.hollowCubeIso

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCube_anodyne
#check @SerrePositivity.InfinityCategories.Coherent.hollowCube_anodyne

#print axioms SerrePositivity.InfinityCategories.Coherent.mem_hollowCube_endpoints_iff
#check @SerrePositivity.InfinityCategories.Coherent.mem_hollowCube_endpoints_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCube_extension
#check @SerrePositivity.InfinityCategories.Coherent.hollowCube_extension

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCylinder
#check @SerrePositivity.InfinityCategories.Coherent.hollowCylinder

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCylinder_anodyne
#check @SerrePositivity.InfinityCategories.Coherent.hollowCylinder_anodyne

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCylinder_extension
#check @SerrePositivity.InfinityCategories.Coherent.hollowCylinder_extension

#print axioms SerrePositivity.InfinityCategories.Coherent.hornVertex
#check @SerrePositivity.InfinityCategories.Coherent.hornVertex

#print axioms SerrePositivity.InfinityCategories.Coherent.hornObj
#check @SerrePositivity.InfinityCategories.Coherent.hornObj

#print axioms SerrePositivity.InfinityCategories.Coherent.horn_map_const
#check @SerrePositivity.InfinityCategories.Coherent.horn_map_const

#print axioms SerrePositivity.InfinityCategories.Coherent.simplex_map_obj
#check @SerrePositivity.InfinityCategories.Coherent.simplex_map_obj

#print axioms SerrePositivity.InfinityCategories.Coherent.horn_simplex_obj
#check @SerrePositivity.InfinityCategories.Coherent.horn_simplex_obj

#print axioms SerrePositivity.InfinityCategories.Coherent.horn_face_obj
#check @SerrePositivity.InfinityCategories.Coherent.horn_face_obj

#print axioms SerrePositivity.InfinityCategories.Coherent.simplex_map_hom
#check @SerrePositivity.InfinityCategories.Coherent.simplex_map_hom

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomOnCell
#check @SerrePositivity.InfinityCategories.Coherent.hornHomOnCell

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomOnCell_transport_back
#check @SerrePositivity.InfinityCategories.Coherent.hornHomOnCell_transport_back

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomOnCell_heq
#check @SerrePositivity.InfinityCategories.Coherent.hornHomOnCell_heq

#print axioms SerrePositivity.InfinityCategories.Coherent.hornHomOnCell_naturality
#check @SerrePositivity.InfinityCategories.Coherent.hornHomOnCell_naturality

#print axioms SerrePositivity.InfinityCategories.Coherent.path_hom_iff
#check @SerrePositivity.InfinityCategories.Coherent.path_hom_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathOfInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathOfInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInterior_pathOfInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathInterior_pathOfInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathOfInterior_pathInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathOfInterior_pathInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInteriorEquiv
#check @SerrePositivity.InfinityCategories.Coherent.pathInteriorEquiv

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInterior_subset_iff
#check @SerrePositivity.InfinityCategories.Coherent.pathInterior_subset_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.pathPrefix
#check @SerrePositivity.InfinityCategories.Coherent.pathPrefix

#print axioms SerrePositivity.InfinityCategories.Coherent.pathSuffix
#check @SerrePositivity.InfinityCategories.Coherent.pathSuffix

#print axioms SerrePositivity.InfinityCategories.Coherent.pathPrefix_comp_pathSuffix
#check @SerrePositivity.InfinityCategories.Coherent.pathPrefix_comp_pathSuffix

#print axioms SerrePositivity.InfinityCategories.Coherent.pathAvoids
#check @SerrePositivity.InfinityCategories.Coherent.pathAvoids

#print axioms SerrePositivity.InfinityCategories.Coherent.pathFaceMap
#check @SerrePositivity.InfinityCategories.Coherent.pathFaceMap

#print axioms SerrePositivity.InfinityCategories.Coherent.pathFacePreimage
#check @SerrePositivity.InfinityCategories.Coherent.pathFacePreimage

#print axioms SerrePositivity.InfinityCategories.Coherent.pathFacePreimageFunctor
#check @SerrePositivity.InfinityCategories.Coherent.pathFacePreimageFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.range_pathFaceMap
#check @SerrePositivity.InfinityCategories.Coherent.range_pathFaceMap

#print axioms SerrePositivity.InfinityCategories.Coherent.pathFaceMap_mono
#check @SerrePositivity.InfinityCategories.Coherent.pathFaceMap_mono

#print axioms SerrePositivity.InfinityCategories.Coherent.pathFaceIso
#check @SerrePositivity.InfinityCategories.Coherent.pathFaceIso

#print axioms SerrePositivity.InfinityCategories.Coherent.pathFaceIso_hom_ι
#check @SerrePositivity.InfinityCategories.Coherent.pathFaceIso_hom_ι

#print axioms SerrePositivity.InfinityCategories.Coherent.pathHollow
#check @SerrePositivity.InfinityCategories.Coherent.pathHollow

#print axioms SerrePositivity.InfinityCategories.Coherent.mem_pathHollow_iff
#check @SerrePositivity.InfinityCategories.Coherent.mem_pathHollow_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.pathHollow_anodyne
#check @SerrePositivity.InfinityCategories.Coherent.pathHollow_anodyne

#print axioms SerrePositivity.InfinityCategories.Coherent.pathHollow_extension
#check @SerrePositivity.InfinityCategories.Coherent.pathHollow_extension

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInteriorFunctor
#check @SerrePositivity.InfinityCategories.Coherent.pathInteriorFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.pathOfInteriorFunctor
#check @SerrePositivity.InfinityCategories.Coherent.pathOfInteriorFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInteriorFunctor_comp_pathOfInteriorFunctor
#check @SerrePositivity.InfinityCategories.Coherent.pathInteriorFunctor_comp_pathOfInteriorFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.pathOfInteriorFunctor_comp_pathInteriorFunctor
#check @SerrePositivity.InfinityCategories.Coherent.pathOfInteriorFunctor_comp_pathInteriorFunctor

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInteriorNerveIso
#check @SerrePositivity.InfinityCategories.Coherent.pathInteriorNerveIso

#print axioms SerrePositivity.InfinityCategories.Coherent.subcomplexPreimageIso
#check @SerrePositivity.InfinityCategories.Coherent.subcomplexPreimageIso

#print axioms SerrePositivity.InfinityCategories.Coherent.subcomplexPreimageArrowIso
#check @SerrePositivity.InfinityCategories.Coherent.subcomplexPreimageArrowIso

#print axioms SerrePositivity.InfinityCategories.Coherent.anodyne_subcomplexPreimage
#check @SerrePositivity.InfinityCategories.Coherent.anodyne_subcomplexPreimage
