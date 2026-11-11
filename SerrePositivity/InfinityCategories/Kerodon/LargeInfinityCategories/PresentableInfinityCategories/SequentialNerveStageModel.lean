module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialNerveStages
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FinitePosetNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：可算鎖の有限始区間を同じ有限順序圏の nerve と同定する。
方針：全単体の各頂点に上界の証明を付け外しする。
規約：同型は元の有限鎖全体に作用する。
使われ方：filtered 性による可算図式の有限段階の延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：有限始区間を上界付き有限順序圏へ写す。
方針：各頂点を Fin (n+1) の元として読む。
規約：全高次単体の関手を保持する。
使われ方：始区間の有限性の移送。 -/
def sequentialNerveStageToFinite (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (n + 1))) where
  app _ := ↾fun s ↦
    { obj i := ULift.up ⟨(s.val.obj i).down, Nat.lt_succ_iff.mpr (s.property i)⟩
      map f := homOfLE (leOfHom (s.val.map f)) }
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 概要：有限鎖の nerve を元の可算鎖の始区間へ戻す。
方針：有限頂点の値を自然数として読み、上界を記録する。
規約：元の可算 nerve への包含と整合する。
使われ方：有限始区間の表示同型の逆。 -/
def sequentialNerveFiniteToStage (n : ℕ) :
    nerve (ULift.{u} (Fin (n + 1))) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) where
  app _ := ↾fun s ↦ ⟨
    { obj i := ULift.up (s.obj i).down.val
      map f := homOfLE (leOfHom (s.map f)) },
    fun i ↦ Nat.le_of_lt_succ (s.obj i).down.isLt⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 概要：可算鎖の有限始区間は有限順序圏の同じ nerve と同型。
方針：上界の証明の付け外しが全次数で互いに逆であることを示す。
規約：頂点だけの同値で代用しない。
使われ方：有限性と quasicategory 性を元の始区間に移す。 -/
def sequentialNerveStageIso (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) ≅ nerve (ULift.{u} (Fin (n + 1))) where
  hom := sequentialNerveStageToFinite n
  inv := sequentialNerveFiniteToStage n
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 概要：各有限始区間は有限単体集合。
方針：有限 poset の nerve の有限性を表示同型で移す。
規約：有限性は非退化単体の全体について主張する。
使われ方：filtered 性の試験形状に使う。 -/
instance sequentialNerveStage_finite (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}).Finite :=
  SSet.finite_of_iso (sequentialNerveStageIso n).symm

/-- 概要：各有限始区間を標準単体と同定する。
方針：有限順序圏の nerve の標準表示を合成する。
規約：宇宙を変更しない。
使われ方：join 余錐による次の有限段階への延長。 -/
def sequentialNerveStageSimplexIso (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} n : SSet.{u}) ≅ Δ[n] :=
  sequentialNerveStageIso n ≪≫ (stdSimplex.isoNerve n).symm

/-- 概要：始区間の包含は標準単体の最終頂点を除く面に一致する。
方針：全単体を表す順序写像の値を計算する。
規約：全射の厳密な等式。
使われ方：余錐を次の段階へ輸送しても前段階を保持する。 -/
lemma sequentialNerveStageSimplexIso_transition (n : ℕ) :
    Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (Nat.le_succ n)) ≫
      (sequentialNerveStageSimplexIso.{u} (n + 1)).hom =
    (sequentialNerveStageSimplexIso.{u} n).hom ≫ SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
