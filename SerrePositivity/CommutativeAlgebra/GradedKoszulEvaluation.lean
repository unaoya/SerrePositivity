module

public import SerrePositivity.CommutativeAlgebra.GradedKoszul
public import SerrePositivity.CommutativeAlgebra.AdicModuleProduct

/-! # Koszul 項の次数成分における係数射の像と単射性

係数加群の射が各次数で持つ像・単射性は、単一複体と反復錐による Koszul 構成の
各項でも保たれる。また、係数の次数成分が I^nM なら、各項の同じ次数成分は I^nK^q。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.GradedKoszulEvaluation

open CategoryTheory GradedKoszul

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M T : ModuleCat.{u} S}

/-- Koszul 射の各項を係数環上の線形射として見る。 -/
def termMap {h : ℕ} (x : Fin h → S) (f : M ⟶ T) (q : ℤ) :
    (underlyingComplex (R := R) x M).X q →ₗ[R] (underlyingComplex (R := R) x T).X q :=
  ((ModuleCat.restrictScalars (algebraMap R S)).map (((koszulModuleFunctor x).map f).f q)).hom

private theorem single_conjugation (x : Fin 0 → S) (f : M ⟶ T) :
    (termMap (R := R) x f 0).comp
      (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M 0 rfl)).toLinearEquiv.symm.toLinearMap) =
      (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (HomologicalComplex.singleObjXIsoOfEq
          (.up ℤ) 0 T 0 rfl)).toLinearEquiv.symm.toLinearMap).comp
          ((ModuleCat.restrictScalars (algebraMap R S)).map f).hom := by
  apply LinearMap.ext
  intro m
  change (((HomologicalComplex.single _ (.up ℤ) 0).map f).f 0)
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv m) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).inv (f m)
  rw [HomologicalComplex.single_map_f_self]
  simp

private theorem cone_conjugation {h : ℕ} (x : Fin (h + 1) → S) (f : M ⟶ T) (q : ℤ) :
    (termMap (R := R) x f q).comp
      (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm.toLinearMap =
      (coneTermEquiv (R := R) (x (Fin.last h))
        (moduleComplex (Fin.init x) T) q).symm.toLinearMap.comp
        ((termMap (R := R) (Fin.init x) f (q + 1)).prodMap
          (termMap (R := R) (Fin.init x) f q)) := by
  apply LinearMap.ext
  intro m
  apply (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q).injective
  have hn := scalarConeXIsoProd_hom_naturality (x (Fin.last h))
    ((koszulModuleFunctor (Fin.init x)).map f) q
  have he := congrArg (fun g ↦ g.hom
    ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) hn
  change (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q)
      (termMap x f q
        ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) =
    ((termMap (Fin.init x) f (q + 1)).prodMap (termMap (Fin.init x) f q))
      ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q)
        ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) at he
  change (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q)
      (termMap x f q
        ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm m)) =
    (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q)
      ((coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) T) q).symm
        (((termMap (Fin.init x) f (q + 1)).prodMap (termMap (Fin.init x) f q)) m))
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply] using he

/-- 係数の次数成分の像を、全ての Koszul 項の同じ次数成分へ移す。 -/
theorem map_termGrade {h : ℕ} (x : Fin h → S) (f : M ⟶ T)
    (NM : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (NT : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj T))
    (hmap : ∀ n, (NM n).map ((ModuleCat.restrictScalars (algebraMap R S)).map f).hom = NT n)
    (q : ℤ) (n : ℕ) :
    (termGrade x M NM q n).map (termMap (R := R) x f q) = termGrade x T NT q n := by
  induction h generalizing q with
  | zero =>
      by_cases hq : q = 0
      · subst q
        change ((NM n).map (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
          (HomologicalComplex.singleObjXIsoOfEq
            (.up ℤ) 0 M 0 rfl)).toLinearEquiv.symm.toLinearMap)).map
            (termMap x f 0) = (NT n).map
          (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
            (HomologicalComplex.singleObjXIsoOfEq
              (.up ℤ) 0 T 0 rfl)).toLinearEquiv.symm.toLinearMap)
        rw [← Submodule.map_comp, single_conjugation, Submodule.map_comp, hmap]
      · simp only [termGrade, dite_eq_right hq, Submodule.map_bot]
  | succ h ih =>
      rw [termGrade, termGrade, ← Submodule.map_comp, cone_conjugation,
        Submodule.map_comp, LinearMap.prodMap_map_prod, ih (Fin.init x) (q + 1), ih (Fin.init x) q]

/-- 係数の各次数成分上の単射性を、全ての Koszul 項へ移す。 -/
theorem injOn_termGrade {h : ℕ} (x : Fin h → S) (f : M ⟶ T)
    (NM : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (hinj : ∀ n, Set.InjOn ((ModuleCat.restrictScalars (algebraMap R S)).map f).hom (NM n))
    (q : ℤ) (n : ℕ) : Set.InjOn (termMap (R := R) x f q) (termGrade x M NM q n) := by
  induction h generalizing q with
  | zero =>
      by_cases hq : q = 0
      · subst q
        intro a ha b hb hab
        simp only [termGrade] at ha hb
        obtain ⟨a', ha', rfl⟩ := ha
        obtain ⟨b', hb', rfl⟩ := hb
        have hc := single_conjugation (R := R) x f
        have hab' := hab
        have hca := DFunLike.congr_fun hc a'
        have hcb := DFunLike.congr_fun hc b'
        have hab'' := hca.symm.trans (hab'.trans hcb)
        have hh :=
          (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
            (HomologicalComplex.singleObjXIsoOfEq
              (.up ℤ) 0 T 0 rfl)).toLinearEquiv.symm).injective hab''
        exact congrArg _ (hinj n ha' hb' hh)
      · intro a ha b hb _
        simp only [termGrade, dite_eq_right hq] at ha hb
        exact ha.trans hb.symm
  | succ h ih =>
      intro a ha b hb hab
      simp only [termGrade] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hc := cone_conjugation (R := R) x f q
      have hab' := hab
      have hca := DFunLike.congr_fun hc a'
      have hcb := DFunLike.congr_fun hc b'
      have hab'' := hca.symm.trans (hab'.trans hcb)
      have hh := (coneTermEquiv (R := R) (x (Fin.last h))
        (moduleComplex (Fin.init x) T) q).symm.injective hab''
      have hfst := ih (Fin.init x) (q + 1) ha'.1 hb'.1 (congrArg Prod.fst hh)
      have hsnd := ih (Fin.init x) q ha'.2 hb'.2 (congrArg Prod.snd hh)
      exact congrArg _ (Prod.ext hfst hsnd)

/-- イデアル倍の係数成分は、全 Koszul 項で同じイデアル倍になる。 -/
theorem termGrade_ideal_smul_top {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (J : ℕ → Ideal R) (q : ℤ) (n : ℕ) :
    termGrade x M (fun k ↦ J k • ⊤) q n =
      (J n • ⊤ : Submodule R ((underlyingComplex (R := R) x M).X q)) := by
  induction h generalizing q with
  | zero =>
      by_cases hq : q = 0
      · simp only [termGrade, dite_eq_left hq, Submodule.map_smul'', Submodule.map_top]
        rw [LinearMap.range_eq_top.mpr (LinearEquiv.surjective _)]
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq
        let : Subsingleton ((underlyingComplex (R := R) x M).X q) :=
          ModuleCat.subsingleton_of_isZero
            ((ModuleCat.restrictScalars (algebraMap R S)).map_isZero hz)
        simp only [termGrade, dite_eq_right hq]
        exact Submodule.eq_bot_of_subsingleton.symm
  | succ h ih =>
      rw [termGrade, ih (Fin.init x) (q + 1), ih (Fin.init x) q,
        ← AdicModuleProduct.smul_top_prod, Submodule.map_smul'', Submodule.map_top]
      rw [LinearMap.range_eq_top.mpr (LinearEquiv.surjective _)]

end SerrePositivity.GradedKoszulEvaluation
