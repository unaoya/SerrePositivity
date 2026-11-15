module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorLinearAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementSelected
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexNaturality

/-!
概要：元の最大点付き選択 cochain の正次成分は、同じ実 augmentation で零になる。
方針：添字等式による輸送を同じ後合成と両立させ、元の普遍線形成分の消滅を使う。
規約：元の augmentation・次数・符号を保つ。使われ方：大域 augmentation 三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)
lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).f k
      (strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) = 0 := by
  have ht : ∀ (i j : Fin (n + 1)) (h : i = j)
      (v : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)) k),
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj j))).f k
        (cast (congrArg (fun z => (GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj z)) k : Type u)) h) v) =
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i))).f k v := by
    intro i j h v
    subst j
    rfl
  have hcard : J.card = J.card - 1 + 1 := by have := Finset.card_pos.mpr hJ; omega
  have hd : k = 1 - ((Finset.univ : Finset (Fin (J.card - 1 + 1))).card : ℤ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hk
  have hz := strictRawModuleTensorElementLinear_augmentation_zero A X P Q
    ((SimplexCategory.toCat.map (strictRawModuleTensorElementSelection J hJ)).toFunctor ⋙ c)
    Finset.univ k (by simpa only [Finset.card_univ, Fintype.card_fin, ← hcard] using hc) hd
  exact (ht _ _ (strictRawModuleTensorElementSelection_last J hJ)
    (strictRawModuleTensorElementSelectedCochain A X P Q c J k hJ hk)).trans hz

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_smul_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) (r : ℤˣ) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).f k
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) = 0 := by
  simp only [Units.smul_def, map_zsmul,
    strictRawModuleTensorElementSelectedCochainAtMax_augmentation_zero A X P Q c J k hJ hk hc,
    smul_zero]

lemma strictRawModuleTensorElementSelectedCochainAtMax_augmentation_compose_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : 2 ≤ J.card) (r : ℤˣ) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (J.max' hJ)))).val
      (r • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c J k hJ hk) (add_zero k) = 0 := by
  rw [modulePostcompose_graded]
  exact strictRawModuleTensorElementSelectedCochainAtMax_augmentation_smul_zero A X P Q c J k hJ hk hc r

end SerrePositivity.EInfinity.BarrattEccles
