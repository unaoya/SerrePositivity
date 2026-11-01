module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration

/-! # graph導来延長のperfect・compact対象の保存

## 概要
graph導来延長のperfect・compact対象の保存。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

lemma dgDerivedExtension_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((dgDerivedExtension A D E F).obj X) := by
  let P := (modulePerfect A E).inverseImage (dgDerivedExtension A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A E).prop_of_retract (r.map (dgDerivedExtension A D E F)) hY⟩
  apply ((modulePerfect_le_iff_generators A D P).2 ?_) X hX
  intro d
  exact (modulePerfect A E).prop_of_iso (dgDerivedExtensionRepresentableIso A D E F d).symm
    (modulePerfectOver_representable A E (F.obj d) (Set.mem_univ _))

/-- U13dのcompact⇒perfectを再利用する。追加のcompact生成入力は要らない。 -/
lemma dgDerivedExtension_compact {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    moduleCompact A E ((dgDerivedExtension A D E F).obj X) :=
  modulePerfect_compact A E (dgDerivedExtension_perfect A D E F (moduleCompact_perfect A D hX))

end SerrePositivity.DifferentialGraded
