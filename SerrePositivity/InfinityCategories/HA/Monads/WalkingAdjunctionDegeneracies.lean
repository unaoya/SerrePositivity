module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicReindexing

/-!
概要：実際の退化写像の有限順序関手を構成し、全随伴の原子性の保存を証明する。
方針：単体圏の退化と面の実切断と、再添字付けの原子性の保存を使う。
規約：退化は元のHomのnerveの退化と同じもの。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴のsimplicial computadの条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：単体圏の実射の有限順序関手。
方針：元の有限単調射から順序圏の関手を作る。
規約：全射の作用を保持する。使われ方：Riehl–Verity Definition 2.1.4 の単体作用。 -/
def walkingAdjunctionSimplexFunctor {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    Fin (m + 1) ⥤ Fin (n + 1) := f.toOrderHom.monotone.functor

/-- 概要：単体圏の恒等射の有限順序関手は恒等関手。
方針：対象と薄い順序圏の全射を比較する。規約：同じ有限順序集合。
使われ方：Riehl–Verity Definition 2.1.4 の単体作用。 -/
lemma walkingAdjunctionSimplexFunctor_id (n : ℕ) :
    walkingAdjunctionSimplexFunctor (𝟙 ⦋n⦌) = 𝟭 (Fin (n + 1)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  exact Subsingleton.elim _ _

/-- 概要：単体圏の合成は有限順序関手の合成と一致する。
方針：対象と薄い順序圏の全射を比較する。規約：全単体作用の順序。
使われ方：Riehl–Verity Definition 2.1.4。 -/
lemma walkingAdjunctionSimplexFunctor_comp {l m n : ℕ}
    (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) :
    walkingAdjunctionSimplexFunctor f ⋙ walkingAdjunctionSimplexFunctor g =
      walkingAdjunctionSimplexFunctor (f ≫ g) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  exact Subsingleton.elim _ _

/-- 概要：退化の有限順序関手は実際の面の切断を持つ。
方針：単体圏の第三単体恒等式を有限順序関手に写す。
規約：切断の存在は仮定しない。使われ方：Riehl–Verity Proposition 3.1.10 の退化。 -/
lemma walkingAdjunctionDegeneracy_section (n : ℕ) (i : Fin (n + 1)) :
    walkingAdjunctionSimplexFunctor (SimplexCategory.δ i.castSucc) ⋙
      walkingAdjunctionSimplexFunctor (SimplexCategory.σ i) = 𝟭 (Fin (n + 1)) := by
  calc
    _ = walkingAdjunctionSimplexFunctor (SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ i) :=
      walkingAdjunctionSimplexFunctor_comp _ _
    _ = walkingAdjunctionSimplexFunctor (𝟙 ⦋n⦌) :=
      congrArg (fun f : ⦋n⦌ ⟶ ⦋n⦌ => walkingAdjunctionSimplexFunctor f)
        SimplexCategory.δ_comp_σ_self
    _ = _ := walkingAdjunctionSimplexFunctor_id n

/-- 概要：各次数の実圏の退化関手。
方針：実退化の有限順序関手で再添字付けする。
規約：同じ二対象を保つ。使われ方：Riehl–Verity Definition 2.1.4。 -/
def walkingAdjunctionDegeneracyFunctor (n : ℕ) (i : Fin (n + 1)) :
    WalkingAdjunctionLevel n ⥤ WalkingAdjunctionLevel (n + 1) :=
  walkingAdjunctionLevelReindex (walkingAdjunctionSimplexFunctor (SimplexCategory.σ i))

/-- 概要：実退化関手は原子的な全n射を原子的な全(n+1)射へ送る。
方針：実際の面の切断と検証済みの再添字付けの法則を使う。
規約：原子性の保存は仮定しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionDegeneracyFunctor_map_atomic (n : ℕ) (i : Fin (n + 1))
    {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) (hf : WalkingAdjunctionLevelIsAtomic F) :
    WalkingAdjunctionLevelIsAtomic ((walkingAdjunctionDegeneracyFunctor n i).map F) :=
  walkingAdjunctionLevelIsAtomic_precomp_of_split
    (walkingAdjunctionSimplexFunctor (SimplexCategory.σ i))
    (walkingAdjunctionSimplexFunctor (SimplexCategory.δ i.castSucc)) F
    (walkingAdjunctionDegeneracy_section n i) hf

/-- 概要：元の全Homのnerveの退化は構成した有限順序関手での前合成そのもの。
方針：nerveと宇宙持ち上げの実定義を使う。
規約：元の単体集合の作用を保持する。使われ方：Riehl–Verity Definition 2.1.4。 -/
lemma walkingAdjunctionHomShape_degeneracy {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (i : Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    (((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.σ i).op) (ULift.up F)).down =
      walkingAdjunctionSimplexFunctor (SimplexCategory.σ i) ⋙ F := rfl

/-- 概要：元の全Homの単体集合の実退化で原子性が保たれる。
方針：元の退化を実再添字付けに照合し、実切断からの原子性の保存を適用する。
規約：nerveの全作用上の結論。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionHomShape_degeneracy_atomic {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (i : Fin (n + 1)) (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hf : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) F) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      ((((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.σ i).op) (ULift.up F)).down) := by
  rw [walkingAdjunctionHomShape_degeneracy]
  exact walkingAdjunctionDegeneracyFunctor_map_atomic n i F hf

end SerrePositivity.InfinityCategories.HA.Monads
