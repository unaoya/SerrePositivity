module
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.NerveInclusionSimplex

/-!
# 同じ加群 dg 単体の全成分と両立する augmentation

概要：元の閉射と全斉次成分の合成則を束ねる。
方針：対象の包装を明記し、元の Hom end の全次数を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、全有限部分集合を保持する。
使われ方：M10 の同じ元の cone に終端を加える構成の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の加群単体の全斉次成分と厳密に両立する指定閉射。
方針：元の全合成則をそのまま記録する。
規約：HA 1.3.1.6、同じ dg 単体。使われ方：同じ右 cone の係数。 -/
structure ModuleSimplexAugmentation {n : ℕ} (s : Simplex A (RightModule A D) n)
    (M : ModuleCategory A D) where
  app : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ⟶ M
  hom_naturality : ∀ (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
      (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
      (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)),
      compose A (closedHomEquiv A (RightModule A D) _ _ (app b)).val
        (s.hom I a b k hI ha hb hk) (add_zero k) = closedNerveHom (app a) k

/-- 概要：同じ augmentation の閉零 cochain。
方針：元の閉射の同じ Hom end 表示を取る。
規約：HA 1.3.1.6、元の射。使われ方：同じ終端成分の微分。 -/
def ModuleSimplexAugmentation.cycle {n : ℕ} {s : Simplex A (RightModule A D) n}
    {M : ModuleCategory A D} (η : ModuleSimplexAugmentation A D s M) (i : Fin (n + 1)) :
    zeroCycles (homObject A (RightModule A D) (s.obj i) (ForgetEnrichment.to (Complex A) M)) :=
  closedHomEquiv A (RightModule A D) _ _ (η.app i)

/-- 概要：同じ augmentation の元の cochain は閉じている。
方針：同じ閉零表示の性質を取る。
規約：HA 1.3.1.6、元の微分。使われ方：終端を含む HA 方程式。 -/
lemma ModuleSimplexAugmentation.cycle_closed {n : ℕ} {s : Simplex A (RightModule A D) n}
    {M : ModuleCategory A D} (η : ModuleSimplexAugmentation A D s M) (i : Fin (n + 1)) :
    differential A (ModuleSimplexAugmentation.cycle A D η i).val = 0 :=
  (ModuleSimplexAugmentation.cycle A D η i).property

end SerrePositivity.EInfinity.Modules
