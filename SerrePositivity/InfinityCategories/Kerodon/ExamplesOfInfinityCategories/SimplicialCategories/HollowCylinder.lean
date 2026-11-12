module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Kan 複体への空洞立方体の延長

概要：Q の任意の部分単体集合 A に対し、(A×Δ[1])∪(Q×{1}) からの写像を延長する。
方針：包含を anodyne と単射の pushout-product として扱う。
規約：Mathlib の包含座標では既知の合成面は座標 1。Λ[1,1] は {1} である。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.12（Tag 00LV） の空洞立方体の充填に使う。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {Q : SSet.{u}}

/-- 概要：既知部分 (A×Δ[1])∪(Q×{1}) を定義する。
方針：Mathlib の unionProd を使う。
規約：A が立方体の境界なら上面だけを残した空洞立方体。
使われ方：Kerodon 2.4.5.12（Tag 00LV） の包含規約での延長問題。 -/
def hollowCylinder (A : Q.Subcomplex) : (Q ⊗ Δ[1]).Subcomplex :=
  A.unionProd Λ[1, (1 : Fin 2)]

/-- 概要：空洞柱の包含は anodyne。
方針：単射と一辺のホーン包含の pushout-product を使う。
規約：Q と A に有限性・可縮性などを仮定しない。
使われ方：Kerodon 2.4.5.12（Tag 00LV） の空洞立方体を含む一般形。 -/
lemma hollowCylinder_anodyne (A : Q.Subcomplex) :
    SSet.anodyneExtensions (hollowCylinder A).ι :=
  SSet.anodyneExtensions_unionProd_ι A _ (SSet.anodyneExtensions.horn_ι _)

/-- 概要：Kan 複体への空洞柱上の写像は全体へ延長する。
方針：anodyne 包含と終対象への Kan fibration の持ち上げを取る。
規約：存在する延長には A と上面での一致が含まれる。
使われ方：Kerodon 2.4.5.12（Tag 00LV） により局所 Kan 性から coherent nerve の未知 Hom を埋める。 -/
lemma hollowCylinder_extension (A : Q.Subcomplex) {X : SSet.{u}} [SSet.KanComplex X]
    (f : (hollowCylinder A : SSet) ⟶ X) :
    ∃ g : Q ⊗ Δ[1] ⟶ X, (hollowCylinder A).ι ≫ g = f := by
  have : HasLiftingProperty (hollowCylinder A).ι (terminal.from X) :=
    hollowCylinder_anodyne A _ (by rwa [← fibration_iff])
  let sq : CommSq f (hollowCylinder A).ι (terminal.from X) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
