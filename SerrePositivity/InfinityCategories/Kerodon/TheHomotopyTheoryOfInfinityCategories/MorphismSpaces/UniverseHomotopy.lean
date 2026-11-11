module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-!
# 宇宙の持ち上げによる単体的ホモトピーの保存

概要：単体集合の ULift は実際のホモトピーとホモトピー逆を保存する。
方針：区間の単体の持ち上げだけを戻して元のホモトピーを評価する。
規約：元の単体集合の Kan 性は不要。
使われ方：HA 1.3.1.17 の小さい Hom と coherent nerve の宇宙の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 概要：単体的ホモトピーを大きい宇宙の単体集合の間へ持ち上げる。
方針：始域の単体と区間の単体を小さい宇宙へ戻して元の射を評価し、値を持ち上げる。
規約：全次数の自然性と両端をそのまま保つ。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE） の標準 Hom の比較を大きい写像空間へ移す。 -/
def uliftHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.uliftFunctor.{v, u}.map f) (SSet.uliftFunctor.{v, u}.map g) where
  h :=
    { app d := ↾fun z ↦ ULift.up (H.h.app d (z.1.down, ULift.up z.2.down))
      naturality {a b} α := by
        apply ConcreteCategory.hom_ext
        intro z
        apply ULift.ext
        exact congrArg (fun q : (X ⊗ Δ[1]).obj a ⟶ Y.obj b ↦
          q (show (X ⊗ Δ[1]).obj a from (z.1.down, ULift.up z.2.down))) (H.h.naturality α) }
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ d) z.down
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ d) z.down
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.2

/-- 概要：宇宙の持ち上げは実際の単体的ホモトピー逆の存在を保つ。
方針：逆射を関手で写し、二つの合成のホモトピーをそれぞれ持ち上げる。
規約：Kan 性や宇宙の大小の追加条件は不要。
使われ方：HA 1.3.1.17 の解像の比較から実際の coherent pinched Hom への移送。 -/
lemma ulift_homotopyEquivalence {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (SSet.uliftFunctor.{v, u}.map f) := by
  obtain ⟨g, ⟨H⟩, ⟨G⟩⟩ := hf
  refine ⟨SSet.uliftFunctor.map g, ?_, ?_⟩
  · have h := uliftHomotopy.{u, v} H
    simpa only [Functor.map_comp, Functor.map_id] using ⟨h⟩
  · have h := uliftHomotopy.{u, v} G
    simpa only [Functor.map_comp, Functor.map_id] using ⟨h⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
