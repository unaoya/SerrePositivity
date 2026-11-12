module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RingComplexColimits
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
概要：K-projective 複体の余積・次数付き分裂拡大・分裂逐次余極限の閉性。
方針：一点加群の同じ実 Hom end と全射 tower の極限を使う。
規約：任意の filtered 余極限の閉性は主張しない。
使われ方：固定 cell source の Hom 複体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A]

lemma complexSphere_isKProjective (n : ℤ) : (complexSphere A n).IsKProjective :=
  isKProjective_of_homComplex_acyclic A _ (fun _ hN => complexSphereHom_acyclic A _ n hN)

lemma complexCoproduct_isKProjective {I : Type w} [Small.{u} I]
    (P : I → Complex A) (hP : ∀ i, (P i).IsKProjective) : (∐ P).IsKProjective := by
  apply (ringModule_homotopicallyProjective_iff A (ringModule A (∐ P))).1
  exact moduleHomotopicallyProjective_of_iso A PUnit.{1}
    (PreservesCoproduct.iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexFunctor A) P).symm
    (moduleCoproduct_homotopicallyProjective A PUnit.{1} _
      (fun i => (ringModule_homotopicallyProjective_iff A (ringModule A (P i))).2 (hP i)))

lemma complexDegreewiseSplit_isKProjective (S : ShortComplex (Complex A))
    (s : ∀ n : ℤ, (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting)
    (h₁ : S.X₁.IsKProjective) (h₃ : S.X₃.IsKProjective) : S.X₂.IsKProjective := by
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexGradedSplit A S.f S.g (fun n => (s n).r) (fun n => (s n).s)
    (fun n => (s n).f_r) (fun n => (s n).s_g) (fun n => (s n).s_r) S.zero
    (fun n => (s n).id)
  exact (ringModule_homotopicallyProjective_iff A (ringModule A S.X₂)).1
    (t.homotopicallyProjective A PUnit.{1}
      ((ringModule_homotopicallyProjective_iff A (ringModule A S.X₁)).2 h₁)
      ((ringModule_homotopicallyProjective_iff A (ringModule A S.X₃)).2 h₃))

lemma ringComplexMap_homRestriction_surjective {P Q : Complex A} (f : P ⟶ Q)
    (r : ∀ i, Q.X i ⟶ P.X i) (hr : ∀ i, f.f i ≫ r i = 𝟙 _)
    (T : ModuleCategory A PUnit.{1}) (q : ℤ) :
    Function.Surjective ((eHomWhiskerRight (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap A f) T).f q) := by
  intro z
  let N := ForgetEnrichment.to (Complex A) T
  let ez := ringModuleHomIso A (ringModule A P) N
  let et := ringModuleHomIso A (ringModule A Q) N
  let t : Cochain Q (N.obj (op PUnit.unit)) q :=
    Cochain.mk (fun i j hij => r i ≫ (ez.hom.f q z).v i j hij)
  refine ⟨et.inv.f q t, ?_⟩
  apply moduleHomElement_ext A PUnit.{1}
    (M := ringModule A P) (N := N)
  intro x
  cases x
  erw [moduleHomWhiskerRight_apply_π A PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap A f) q
    (et.inv.f q t) PUnit.unit]
  have ht : et.hom.f q (et.inv.f q t) = t :=
    congrArg (fun k => k.f q t) et.inv_hom_id
  change (Cochain.ofHom ((moduleEvaluation A PUnit.{1} PUnit.unit).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap A f))).comp (et.hom.f q (et.inv.f q t)) (zero_add q) = ez.hom.f q z
  rw [show (moduleEvaluation A PUnit.{1} PUnit.unit).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap A f) = f from
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexMap_evaluation A f, ht]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, t, Cochain.mk_v]
  erw [← Category.assoc, hr, Category.id_comp]

lemma complexSequentialColimit_isKProjective (F : ℕ ⥤ Complex A)
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ n, (F.obj n).IsKProjective)
    (r : ∀ n i, (F.obj (n + 1)).X i ⟶ (F.obj n).X i)
    (hr : ∀ n i, (F.map (homOfLE (Nat.le_succ n))).f i ≫ r n i = 𝟙 _) :
    c.pt.IsKProjective := by
  apply (ringModule_homotopicallyProjective_iff A (ringModule A c.pt)).1
  intro T hT
  apply complexTowerLimit_acyclic A
    (moduleHomSourceDiagram A PUnit.{1} (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexFunctor A) T)
    (moduleColimitHomIsLimit A PUnit.{1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringComplexIsColimit A hc) T)
  · intro n
    exact (ringModule_homotopicallyProjective_iff A (ringModule A (F.obj n))).2 (hF n) T hT
  · intro n q
    exact ringComplexMap_homRestriction_surjective A (F.map (homOfLE (Nat.le_succ n)))
      (r n) (hr n) T q

end SerrePositivity.InfinityCategories.Project.DerivedCategories
