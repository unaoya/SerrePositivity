import SerrePositivity.KST.Comparison

/-!
# K-L2 比較定理の公理監査

概要：現在公開する全宣言の型と推移的な依存公理を確認する。
方針：#check @ と #print axioms を併用する。
規約：許可する公理は propext、Classical.choice、Quot.sound のみ。
使われ方：SS03 (2.9) と KST 式 (2.2) の保存単位。比較定理全体は未完了。
-/

set_option pp.universes true
set_option pp.explicit true

-- ComponentSubcomplex.lean

#check @SerrePositivity.KST.Comparison.componentSubcomplex
#print axioms SerrePositivity.KST.Comparison.componentSubcomplex

#check @SerrePositivity.KST.Comparison.componentVertex
#print axioms SerrePositivity.KST.Comparison.componentVertex

#check @SerrePositivity.KST.Comparison.componentEdge
#print axioms SerrePositivity.KST.Comparison.componentEdge

#check @SerrePositivity.KST.Comparison.componentVertex_sound
#print axioms SerrePositivity.KST.Comparison.componentVertex_sound

#check @SerrePositivity.KST.Comparison.componentClassMap
#print axioms SerrePositivity.KST.Comparison.componentClassMap

#check @SerrePositivity.KST.Comparison.componentClassEquiv
#print axioms SerrePositivity.KST.Comparison.componentClassEquiv

-- DGAlgebra.lean

#check @SerrePositivity.KST.Comparison.DGAlgebraModel
#print axioms SerrePositivity.KST.Comparison.DGAlgebraModel

#check @SerrePositivity.KST.Comparison.DGAlgebraModel.IsConnective
#print axioms SerrePositivity.KST.Comparison.DGAlgebraModel.IsConnective

#check @SerrePositivity.KST.Comparison.dgAlgebraGamma
#print axioms SerrePositivity.KST.Comparison.dgAlgebraGamma

#check @SerrePositivity.KST.Comparison.dgAlgebraComponents
#print axioms SerrePositivity.KST.Comparison.dgAlgebraComponents

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGL
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGL

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGLGroup
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGLGroup

#check @SerrePositivity.KST.Comparison.dgAlgebraHatGLComponents
#print axioms SerrePositivity.KST.Comparison.dgAlgebraHatGLComponents

-- DoldKanGL.lean

#check @SerrePositivity.KST.Comparison.unitsPreimage
#print axioms SerrePositivity.KST.Comparison.unitsPreimage

#check @SerrePositivity.KST.Comparison.evalZeroUnits
#print axioms SerrePositivity.KST.Comparison.evalZeroUnits

#check @SerrePositivity.KST.Comparison.one_add_X_mem_evalZeroUnits
#print axioms SerrePositivity.KST.Comparison.one_add_X_mem_evalZeroUnits

#check @SerrePositivity.KST.Comparison.not_isUnit_one_add_X
#print axioms SerrePositivity.KST.Comparison.not_isUnit_one_add_X

#check @SerrePositivity.KST.Comparison.one_add_X_no_right_inverse
#print axioms SerrePositivity.KST.Comparison.one_add_X_no_right_inverse

#check @SerrePositivity.KST.Comparison.matrixToComponents
#print axioms SerrePositivity.KST.Comparison.matrixToComponents

#check @SerrePositivity.KST.Comparison.matrixToComponents_natural
#print axioms SerrePositivity.KST.Comparison.matrixToComponents_natural

#check @SerrePositivity.KST.Comparison.hatGLSubmonoid
#print axioms SerrePositivity.KST.Comparison.hatGLSubmonoid

#check @SerrePositivity.KST.Comparison.hatGLPullback
#print axioms SerrePositivity.KST.Comparison.hatGLPullback

#check @SerrePositivity.KST.Comparison.hatGLMonoidObject
#print axioms SerrePositivity.KST.Comparison.hatGLMonoidObject

-- GLComponents.lean

#check @SerrePositivity.KST.Comparison.hatGLSpace
#print axioms SerrePositivity.KST.Comparison.hatGLSpace

#check @SerrePositivity.KST.Comparison.matrixToComponents_zero_entry
#print axioms SerrePositivity.KST.Comparison.matrixToComponents_zero_entry

#check @SerrePositivity.KST.Comparison.hatGLCoefficientEdge
#print axioms SerrePositivity.KST.Comparison.hatGLCoefficientEdge

#check @SerrePositivity.KST.Comparison.hatGLEdgeOfCoefficients
#print axioms SerrePositivity.KST.Comparison.hatGLEdgeOfCoefficients

#check @SerrePositivity.KST.Comparison.hatGLVertexUnit
#print axioms SerrePositivity.KST.Comparison.hatGLVertexUnit

#check @SerrePositivity.KST.Comparison.hatGLVertexUnit_edge
#print axioms SerrePositivity.KST.Comparison.hatGLVertexUnit_edge

#check @SerrePositivity.KST.Comparison.hatGLClassMap
#print axioms SerrePositivity.KST.Comparison.hatGLClassMap

#check @SerrePositivity.KST.Comparison.hatGLClassMap_injective
#print axioms SerrePositivity.KST.Comparison.hatGLClassMap_injective

#check @SerrePositivity.KST.Comparison.hatGLClassMap_surjective
#print axioms SerrePositivity.KST.Comparison.hatGLClassMap_surjective

#check @SerrePositivity.KST.Comparison.hatGLComponentsEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLComponentsEquiv

#check @SerrePositivity.KST.Comparison.hatGLComponentsGroup
#print axioms SerrePositivity.KST.Comparison.hatGLComponentsGroup

#check @SerrePositivity.KST.Comparison.hatGLComponentsMulEquiv
#print axioms SerrePositivity.KST.Comparison.hatGLComponentsMulEquiv

#check @SerrePositivity.KST.Comparison.hatGLVertexUnit_mul
#print axioms SerrePositivity.KST.Comparison.hatGLVertexUnit_mul

#check @SerrePositivity.KST.Comparison.hatGL_mk_mul
#print axioms SerrePositivity.KST.Comparison.hatGL_mk_mul

#check @SerrePositivity.KST.Comparison.hatGL_mk_one
#print axioms SerrePositivity.KST.Comparison.hatGL_mk_one

-- GammaRing.lean

#check @SerrePositivity.KST.Comparison.GammaEnd
#print axioms SerrePositivity.KST.Comparison.GammaEnd

#check @SerrePositivity.KST.Comparison.gammaEndRing
#print axioms SerrePositivity.KST.Comparison.gammaEndRing

#check @SerrePositivity.KST.Comparison.gammaEndPullback
#print axioms SerrePositivity.KST.Comparison.gammaEndPullback

#check @SerrePositivity.KST.Comparison.gammaEndRingObject
#print axioms SerrePositivity.KST.Comparison.gammaEndRingObject

#check @SerrePositivity.KST.Comparison.gammaEnd_underlying
#print axioms SerrePositivity.KST.Comparison.gammaEnd_underlying

#check @SerrePositivity.KST.Comparison.gammaEndDoldKanIso
#print axioms SerrePositivity.KST.Comparison.gammaEndDoldKanIso

-- PiZeroRing.lean

#check @SerrePositivity.KST.Comparison.ringSpace
#print axioms SerrePositivity.KST.Comparison.ringSpace

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeAdd
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeAdd

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeMul
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeMul

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeNeg
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeNeg

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeReverse
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeReverse

#check @SerrePositivity.KST.Comparison.SimplicialRing.edgeConcat
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.edgeConcat

#check @SerrePositivity.KST.Comparison.SimplicialRing.nonempty_edge_of_mk_eq
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.nonempty_edge_of_mk_eq

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsAdd
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsAdd

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsMul
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsMul

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsAddInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsAddInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsMulInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsMulInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsZeroInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsZeroInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsOneInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsOneInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsNegInst
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsNegInst

#check @SerrePositivity.KST.Comparison.SimplicialRing.mk_add
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.mk_add

#check @SerrePositivity.KST.Comparison.SimplicialRing.mk_mul
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.mk_mul

#check @SerrePositivity.KST.Comparison.SimplicialRing.mk_neg
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.mk_neg

#check @SerrePositivity.KST.Comparison.SimplicialRing.componentsRing
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.componentsRing

#check @SerrePositivity.KST.Comparison.SimplicialRing.toComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.toComponents

#check @SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents

#check @SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents_natural
#print axioms SerrePositivity.KST.Comparison.SimplicialRing.simplexToComponents_natural

-- SimplexComponents.lean

#check @SerrePositivity.KST.Comparison.simplexVertex
#print axioms SerrePositivity.KST.Comparison.simplexVertex

#check @SerrePositivity.KST.Comparison.simplexVertex_class_eq
#print axioms SerrePositivity.KST.Comparison.simplexVertex_class_eq

#check @SerrePositivity.KST.Comparison.simplexClass
#print axioms SerrePositivity.KST.Comparison.simplexClass

#check @SerrePositivity.KST.Comparison.simplexClass_map
#print axioms SerrePositivity.KST.Comparison.simplexClass_map

#check @SerrePositivity.KST.Comparison.simplexClass_zero
#print axioms SerrePositivity.KST.Comparison.simplexClass_zero
