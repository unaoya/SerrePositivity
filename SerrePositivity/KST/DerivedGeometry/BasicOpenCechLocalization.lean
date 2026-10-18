module

public import SerrePositivity.KST.DerivedGeometry.BasicOpenSectionComparisonIso
public import SerrePositivity.KST.DerivedGeometry.OpenCechIntersection
public import SerrePositivity.KST.DerivedGeometry.BasicOpenLocalization
public import SerrePositivity.KST.DerivedGeometry.MaximalOpenCech

/-!
概要：有限基本開 Čech 複体の局所化比較と正次数の完全性。
方針：有限積の局所化、基本開上の切断比較、最大要素による収縮を合成する。
規約：実際の tilde の切断と Mathlib の Čech 複体を保持する。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}}

/--
概要：有限個の基本開の圏論的積は定義元の積の基本開。
方針：積を有限下限と同定し、基本開の積の公式を有限帰納する。
規約：空積は D(1) として扱う。
使われ方：TT §3、Toën §3.2 の Čech の各交叉が基本開であること。
-/
lemma basicOpen_finiteProduct {J : Type v} [Fintype J] (f : J → R) :
    (∏ᶜ (fun j => basicOpen (f j))) = basicOpen (∏ j, f j) := by
  classical
  have hp : (∏ᶜ (fun j => basicOpen (f j))) =
      Finset.univ.inf (fun j => basicOpen (f j)) := by
    trans Finset.univ.inf ((Discrete.functor (fun j => basicOpen (f j))).obj)
    · exact (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
        (CompleteLattice.finiteLimitCone _).isLimit).to_eq
    · change Finset.univ.inf ((fun j => basicOpen (f j)) ∘ discreteEquiv.toEmbedding) = _
      simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rw [hp]
  have h (s : Finset J) : s.inf (fun j => basicOpen (f j)) = basicOpen (∏ j ∈ s, f j) := by
    induction s using Finset.induction_on with
    | empty => simp [basicOpen_one]
    | @insert j s hj hs => simp [hj, hs, basicOpen_mul]
  simpa using h Finset.univ

/--
概要：有限基本開 Čech 複体に切断の局所化比較を適用した射は同型。
方針：各交叉を基本開と表示し、各成分の切断比較の同型性を使う。
規約：比較は構成済みの自然変換に Čech 関手を適用した射そのもの。
使われ方：TT §3、Toën §3.2 の局所化後の Čech 収縮。
-/
instance basicOpenCech_sectionComparison_isIso (M : ModuleCat.{u} R) (a : R)
    {ι : Type u} (f : ι → R) :
    IsIso ((cechComplexFunctor (fun i => basicOpen (f i))).map
      (sectionLocalizationComparison (tilde M) a)) := by
  classical
  have (n : ℕ) : IsIso (((cechComplexFunctor (fun i => basicOpen (f i))).map
      (sectionLocalizationComparison (tilde M) a)).f n) := by
    have (t : Fin (n + 1) → ι) : IsIso
        ((sectionLocalizationComparison (tilde M) a).app
          (.op (∏ᶜ (fun k => basicOpen (f (t k)))))) := by
      change IsIso (sectionLocalizationComparisonAt (tilde M) a
        (∏ᶜ (fun k => basicOpen (f (t k)))))
      have heq := basicOpen_finiteProduct (R := R) (fun k : Fin (n + 1) => f (t k))
      exact heq.symm ▸ (inferInstance : IsIso (sectionLocalizationComparisonAt (tilde M) a
        (basicOpen (∏ k, f (t k)))))
    change IsIso (Limits.Pi.map (fun t : Fin (n + 1) → ι =>
      (sectionLocalizationComparison (tilde M) a).app
        (.op (∏ᶜ (fun k => basicOpen (f (t k)))))))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/--
概要：有限基本開 Čech 複体を a で局所化すると交叉後の族の Čech 複体と同型。
方針：有限積の比較、切断の局所化比較、交叉の Čech 比較を順に合成する。
規約：交代微分と全次数に対する実際の複体同型。
使われ方：TT §3、Toën §3.2 のアフィン Čech 完全性。
-/
def basicOpenCechLocalizationIso (M : ModuleCat.{u} R) (a : R)
    {ι : Type u} [Finite ι] (f : ι → R) :
    ((moduleLocalizationR (.powers a)).mapHomologicalComplex (.up ℕ)).obj
      ((cechComplexFunctor (fun i => basicOpen (f i))).obj
        (modulesSpecToSheaf.obj (tilde M)).obj) ≅
    (cechComplexFunctor (fun i => basicOpen (f i) ⊓ basicOpen a)).obj
      (modulesSpecToSheaf.obj (tilde M)).obj :=
  finiteCechFunctorIso (moduleLocalizationR (.powers a)) (fun i => basicOpen (f i))
      (modulesSpecToSheaf.obj (tilde M)).obj ≪≫
    asIso ((cechComplexFunctor (fun i => basicOpen (f i))).map
      (sectionLocalizationComparison (tilde M) a)) ≪≫
    basicOpenIntersectionCechComplexIso a (fun i => basicOpen (f i))
      (modulesSpecToSheaf.obj (tilde M)).obj

end SerrePositivity.KST.DerivedGeometry
