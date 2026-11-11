module
public import SerrePositivity.KST.SConstruction.DGOdotTailKernelLowerTriangle
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift
public import SerrePositivity.KST.LocalizingInvariants.CompositionDiagonalTransport

/-!
概要：厚核包含と保存済み実中央辺を持つ下二単体を、同じ固定 S 内で構成する。
方針：元の厳密 dg 二辺の coherent 合成二単体を用い、その全 ν 像を保持する。
規約：外面の下三角形や長方形の下段合成三角形との同定は別の証明を要する。
使われ方：K-S• の上指定二単体と貼る厚核側の実下二単体。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：同じ厚核包含の後に元の実中央辺を合成した固定 S の辺。
方針：保存済み二射の厳密合成。規約：厚核・cell 始域・逆回転基底を保持。
使われ方：下指定二単体の対角辺。 -/
def dgOdotTailKernelLiftComposite :
    dgOdotMilnorFlatKernelInput R d ⟶ dgOdotMilnorRightAxisInput R d :=
  dgOdotMilnorFlatKernelInputMap R d ≫ dgOdotMilnorRightAxisInputMap R d

/-- 概要：厚核包含と実中央辺の三辺を持つ実合成証人。
方針：固定 S の元の合成を coherent nerve に写す。
規約：関手同型だけで二単体の存在を代用しない。使われ方：厚核側の実下二単体。 -/
def dgOdotTailKernelLiftCompStruct : SSet.Edge.CompStruct
    (X := dgKInputInfinity.{u, u + 1} R)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTailKernelLiftComposite R d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgOdotMilnorFlatKernelInputMap R d)
    (dgOdotMilnorRightAxisInputMap R d)

/-- 概要：同じ実合成証人の全二単体。
方針：Yoneda 表示を使う。規約：元の指定二辺と対角辺を選び直さない。
使われ方：実比較面の下三角形として指定する S 内の射。 -/
def dgOdotTailKernelLiftTriangle : (Δ[2] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  SSet.yonedaEquiv.symm (dgOdotTailKernelLiftCompStruct R d).simplex

/-- 概要：同じ下二単体の三面は元包含・元中央辺・元合成辺。
方針：coherent 合成証人の三面を回収する。規約：全一単体の等号。
使われ方：上指定二単体との共有対角・二短辺の照合。 -/
lemma dgOdotTailKernelLiftTriangle_edges :
    stdSimplex.δ (2 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      stdSimplex.δ (0 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d)).edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTailKernelLiftComposite R d)).edge := by
  exact ⟨by rw [dgOdotTailKernelLiftTriangle, stdSimplex.δ_comp_yonedaEquiv_symm,
                (dgOdotTailKernelLiftCompStruct R d).d₂]; rfl,
    by rw [dgOdotTailKernelLiftTriangle, stdSimplex.δ_comp_yonedaEquiv_symm,
           (dgOdotTailKernelLiftCompStruct R d).d₀]; rfl,
    by rw [dgOdotTailKernelLiftTriangle, stdSimplex.δ_comp_yonedaEquiv_symm,
           (dgOdotTailKernelLiftCompStruct R d).d₁]; rfl⟩

/-- 概要：厚核側の同じ全下二単体を Cat^perf へ写す。
方針：元の固定 ν の完備持ち上げで後合成する。
規約：別の合成二単体を選択しない。使われ方：LT の指定下二単体との全比較の実側。 -/
def dgOdotTailKernelLiftPerfectTriangle :
    (Δ[2] : SSet.{u + 2}) ⟶ perfectStableInfinity.{u + 1} :=
  dgOdotTailKernelLiftTriangle R d ≫ dgKInputPerfectNu R

/-- 概要：完備包含後も元の全 ν 二単体を厳密に回収する。
方針：固定 ν の全単体回収則を使う。規約：辺だけの回収ではない。
使われ方：native と Cat^perf の全二単体比較の照合。 -/
lemma dgOdotTailKernelLiftPerfectTriangle_inclusion :
    dgOdotTailKernelLiftPerfectTriangle R d ≫ perfectStableInfinityInclusion =
      dgOdotTailKernelLiftTriangle R d ≫ dgKInputNu R := by
  rw [dgOdotTailKernelLiftPerfectTriangle, Category.assoc, dgKInputPerfectNu_inclusion]

/-- 概要：同じ ν 下二単体の三面は元の三つの完全射の一単体。
方針：実 S の三面回収と固定 ν の辺回収を合成する。
規約：包含・中央辺・合成辺を同時に保持。使われ方：元 LT 下二単体への境界照合。 -/
lemma dgOdotTailKernelLiftTriangle_nu_edges :
    stdSimplex.δ (2 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d ≫ dgKInputNu R =
        SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKInputNuMap R (dgOdotMilnorFlatKernelInputMap R d))).edge ∧
      stdSimplex.δ (0 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d ≫ dgKInputNu R =
        SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKInputNuMap R (dgOdotMilnorRightAxisInputMap R d))).edge ∧
      stdSimplex.δ (1 : Fin 3) ≫ dgOdotTailKernelLiftTriangle R d ≫ dgKInputNu R =
        SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKInputNuMap R (dgOdotTailKernelLiftComposite R d))).edge := by
  have he := dgOdotTailKernelLiftTriangle_edges R d
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg (fun f => f ≫ dgKInputNu R) he.1).trans
      ((SSet.yonedaEquiv_symm_comp
        (X := dgKInputInfinity.{u, u + 1} R)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge (dgKInputNu R)).symm.trans
          (congrArg SSet.yonedaEquiv.symm (dgKInputNu_edge R (dgOdotMilnorFlatKernelInputMap R d))))
  · exact (congrArg (fun f => f ≫ dgKInputNu R) he.2.1).trans
      ((SSet.yonedaEquiv_symm_comp
        (X := dgKInputInfinity.{u, u + 1} R)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d)).edge (dgKInputNu R)).symm.trans
          (congrArg SSet.yonedaEquiv.symm (dgKInputNu_edge R (dgOdotMilnorRightAxisInputMap R d))))
  · exact (congrArg (fun f => f ≫ dgKInputNu R) he.2.2).trans
      ((SSet.yonedaEquiv_symm_comp
        (X := dgKInputInfinity.{u, u + 1} R)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTailKernelLiftComposite R d)).edge (dgKInputNu R)).symm.trans
          (congrArg SSet.yonedaEquiv.symm (dgKInputNu_edge R (dgOdotTailKernelLiftComposite R d))))

variable {k' : (dgKInputInfinity.{u, u + 1} R).Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorRightAxisInput R d))}
  (H : SSet.Edge.CompStruct
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgOdotMilnorFlatKernelInput R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTailKernelLiftComposite R d)) k')

/-- 概要：指定対角が変わる場合、差を認証する元二単体に沿って同じ下二単体を移送する。
方針：Sp 正本の三次元証人を同じ固定 S に特殊化する。
規約：二短辺と元二単体・指定差を全て保持。使われ方：K-S• の対角指定の吸収。 -/
def dgOdotTailKernelLiftDiagonalTransport :
    CompositionDiagonalTransport (dgOdotTailKernelLiftCompStruct R d) H :=
  compositionDiagonalTransport (dgOdotTailKernelLiftCompStruct R d) H

/-- 概要：元二短辺と新指定対角を持つ、同じ三次元証人の移送下二単体。
方針：Sp 正本の第一面を回収する。規約：別の三角形を選び直さない。
使われ方：新指定対角を持つ上二単体との貼り合わせ。 -/
def dgOdotTailKernelLiftTransportedCompStruct : SSet.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d)) k' :=
  (dgOdotTailKernelLiftDiagonalTransport R d H).triangle

/-- 概要：同じ移送四面体は元下二単体・移送下二単体・指定差・元単位面を保持する。
方針：同じ Sp 正本の三面回収と第一面の定義を使う。
規約：元の三次元証人そのもの。使われ方：対角変更後も元指定値を追跡する。 -/
lemma dgOdotTailKernelLiftDiagonalTransport_faces :
    let t := (dgOdotTailKernelLiftDiagonalTransport R d H).simplex
    (dgKInputInfinity R).δ 0 t = (dgOdotTailKernelLiftCompStruct R d).simplex ∧
      (dgKInputInfinity R).δ 1 t = (dgOdotTailKernelLiftTransportedCompStruct R d H).simplex ∧
      (dgKInputInfinity R).δ 2 t = H.simplex ∧
      (dgKInputInfinity R).δ 3 t =
        (SSet.Edge.CompStruct.idComp
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d))).simplex :=
  ⟨(dgOdotTailKernelLiftDiagonalTransport R d H).d₀, rfl,
    (dgOdotTailKernelLiftDiagonalTransport R d H).d₂,
    (dgOdotTailKernelLiftDiagonalTransport R d H).d₃⟩
end SerrePositivity.KST.SConstruction
