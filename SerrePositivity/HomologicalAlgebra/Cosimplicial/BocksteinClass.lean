module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinCochains
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# 正則元による Bockstein とコホモロジーの積

## 概要
Bockstein を持ち上げた余輪体で計算し、平方零と Leibniz 則を示す。

## 方針
短完全列の連結写像の代表元公式を、加群と加法群のホモロジーの比較で移す。

## 規約
余鎖の次数を一つ上げ、右側の項の符号は左因子の次数で決める。

## 使われ方
Hodge–Tate 写像の次数 1 と、その外積への延長。
-/

public section
noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

section ModuleHomology

variable (k : Type u) [CommRing k]
variable (X : CosimplicialObject CommRingCat.{u})
variable (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X)

private abbrev moduleCochains :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (toModules k X ι)

private theorem moduleCochains_d_apply (n : ℕ) (x : (moduleCochains k X ι).X n) :
    (moduleCochains k X ι).d n (n + 1) x = cochainDifferential X n x := by
  let y : X.obj ⦋n⦌ := x
  change (moduleCochains k X ι).d n (n + 1) x = cochainDifferential X n y
  rw [cochainDifferential_apply]
  dsimp only [moduleCochains, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul]
  let M := (toModules k X ι).obj ⦋n⦌
  let N := (toModules k X ι).obj ⦋n + 1⦌
  let z : M := x
  change ((∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • ((toModules k X ι).δ i).hom)
    : M →ₗ[k] N) z = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

private theorem moduleCycle (n : ℕ) (a : Cocycles X n) :
    (moduleCochains k X ι).d n (n + 1) a.1 = 0 :=
  (moduleCochains_d_apply k X ι n a.1).trans
    ((ringCochainComplex_d_apply X n a.1).symm.trans a.2)

private def moduleCycleRep (n : ℕ) (a : Cocycles X n) : (moduleCochains k X ι).cycles n :=
  (moduleCochains k X ι).cyclesMk a.1 (n + 1) (CochainComplex.next ℕ n) (moduleCycle k X ι n a)

private theorem moduleCycleRep_apply (n : ℕ) (a : Cocycles X n) :
    (moduleCochains k X ι).iCycles n (moduleCycleRep k X ι n a) = a.1 :=
  HomologicalComplex.i_cyclesMk (moduleCochains k X ι) a.1 _ _ (moduleCycle k X ι n a)

private theorem cohomologyEquivModuleHomology_class (n : ℕ) (a : Cocycles X n) :
    cohomologyEquivModuleHomology k X ι n (cohomologyClass X n a) =
      (moduleCochains k X ι).homologyπ n (moduleCycleRep k X ι n a) := by
  rw [cohomologyClass_apply]
  let F := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  let K := moduleCochains k X ι
  let L := ringCochainComplex X
  have aux (e : L ≅ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
      (he : e.hom.f n = 𝟙 (L.X n)) :
      ((HomologicalComplex.homologyMap e.hom n ≫ ((K.sc n).mapHomologyIso F).hom)
        : L.homology n ⟶ F.obj (K.homology n))
        (L.homologyπ n (cycleRepresentative X n a)) =
          K.homologyπ n (moduleCycleRep k X ι n a) := by
    erw [← ConcreteCategory.comp_apply, ← Category.assoc, HomologicalComplex.homologyπ_naturality,
      Category.assoc]
    change (HomologicalComplex.cyclesMap e.hom n ≫
      ((K.sc n).map F).homologyπ ≫ ((K.sc n).mapHomologyIso F).hom)
      (cycleRepresentative X n a) = _
    let h := (K.sc n).homologyData.left
    erw [h.mapHomologyIso_eq F, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      ← Category.assoc (((K.sc n).map F).homologyπ),
      (h.map F).homologyπ_comp_homologyIso_hom]
    let ψ := (h.map F).cyclesIso.hom
    have hψ : ψ ≫ F.map h.i = ((K.sc n).map F).iCycles :=
      (h.map F).cyclesIso_hom_comp_i
    have hval : (HomologicalComplex.cyclesMap e.hom n ≫ ψ) (cycleRepresentative X n a) =
        (F.map h.cyclesIso.hom) (moduleCycleRep k X ι n a) := by
      apply (AddCommGrpCat.mono_iff_injective (F.map h.i)).mp inferInstance
      let z : F.obj (K.sc n).cycles := moduleCycleRep k X ι n a
      change (F.map h.i) ((HomologicalComplex.cyclesMap e.hom n ≫ ψ)
        (cycleRepresentative X n a)) = (F.map h.i) (F.map h.cyclesIso.hom z)
      have hz : F.map h.i (F.map h.cyclesIso.hom z) = F.map (K.iCycles n) z := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp,
          ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
        rfl
      rw [hz]
      erw [← ConcreteCategory.comp_apply, Category.assoc, hψ]
      change (HomologicalComplex.cyclesMap e.hom n ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n)
        (cycleRepresentative X n a) = _
      erw [HomologicalComplex.cyclesMap_i, he, Category.comp_id, cycleRepresentative_apply]
      exact (moduleCycleRep_apply k X ι n a).symm
    have hπ : h.cyclesIso.hom ≫ h.π ≫ h.homologyIso.inv = K.homologyπ n := by
      rw [← Category.assoc, ← h.homologyπ_comp_homologyIso_hom, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
      rfl
    change (HomologicalComplex.cyclesMap e.hom n ≫
      (ψ ≫ F.map h.π) ≫ F.map h.homologyIso.inv) (cycleRepresentative X n a) = _
    erw [Category.assoc ψ, ← Category.assoc (HomologicalComplex.cyclesMap e.hom n),
      ConcreteCategory.comp_apply, hval]
    erw [← ConcreteCategory.comp_apply, ← F.map_comp, ← F.map_comp, hπ]
    rfl
  apply aux
  rfl

end ModuleHomology

section Regular

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
  (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))
  (k : Type u) [CommRing k]
  (ιC : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C)

local notation "Q[" j "]" => quotPow C d hd_nat j
local notation "q[" j "]" => quotProjection C d hd_nat j

/-- 指定元で割った余輪体の Bockstein は、余鎖の持ち上げを微分して指定元で割った類。 -/
theorem cupBockstein_class (n : ℕ) (a : Cocycles Q[1] n) (b : Cocycles Q[1] (n + 1))
    (x : C.obj ⦋n⦌) (y : C.obj ⦋n + 1⦌)
    (hx : q[1].app ⦋n⦌ x = a.1) (hy : q[1].app ⦋n + 1⦌ y = b.1)
    (hd : cochainDifferential C n x = d ⦋n + 1⦌ * y) :
    cupBockstein C d hd_nat hd_reg k ιC n (cohomologyClass Q[1] n a) =
      cohomologyClass Q[1] (n + 1) b := by
  let E := cohomologyEquivModuleHomology k Q[1] (ιC ≫ q[1])
  apply (E (n + 1)).injective
  change E (n + 1) ((E (n + 1)).symm
    (regularBockstein C d hd_nat hd_reg k ιC n (E n (cohomologyClass Q[1] n a)))) = _
  rw [AddEquiv.apply_symm_apply]
  simp only [E, cohomologyEquivModuleHomology_class]
  let S := regularShortExact C d hd_nat hd_reg k ιC
  let x₂ : (moduleCochains k Q[2] (ιC ≫ q[2])).X n := q[2].app ⦋n⦌ x
  refine ShortComplex.ShortExact.δ_apply S.cochainShortExact n (n + 1) rfl
    a.1 (moduleCycle k Q[1] _ n a) x₂ ?_ b.1 ?_ (n + 1 + 1)
      (CochainComplex.next ℕ (n + 1))
  · exact hx
  · rw [← hy]
    change Ideal.Quotient.mk (Ideal.span {d ⦋n + 1⦌ ^ 2}) (d ⦋n + 1⦌ * y) =
      (moduleCochains k Q[2] (ιC ≫ q[2])).d n (n + 1) x₂
    rw [moduleCochains_d_apply]
    exact ((cochainDifferential_natural C Q[2] q[2] n x).symm.trans
      (congrArg (q[2].app ⦋n + 1⦌) hd)).symm

private def projectCycle (n : ℕ) (x : C.obj ⦋n⦌)
    (hx : cochainDifferential C n x = 0) : Cocycles Q[1] n :=
  ⟨q[1].app ⦋n⦌ x, by
    change (ringCochainComplex Q[1]).d n (n + 1) (q[1].app ⦋n⦌ x) = 0
    rw [ringCochainComplex_d_apply, ← cochainDifferential_natural C Q[1] q[1], hx, map_zero]
    rfl⟩

private theorem exists_regularCocycleLift (n : ℕ) (a : Cocycles Q[1] n) :
    ∃ (x : C.obj ⦋n⦌) (y : C.obj ⦋n + 1⦌),
      q[1].app ⦋n⦌ x = a.1 ∧ cochainDifferential C n x = d ⦋n + 1⦌ * y := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective a.1
  change q[1].app ⦋n⦌ x = a.1 at hx
  have ha : cochainDifferential Q[1] n a.1 = 0 :=
    (ringCochainComplex_d_apply Q[1] n a.1).symm.trans a.2
  obtain ⟨y, hy⟩ := exists_cochainDifferential_eq_mul C d hd_nat n x (hx ▸ ha)
  exact ⟨x, y, hx, hy⟩

/-- 正則元で定まるコホモロジーの Bockstein は二回適用すると零。 -/
theorem cupBockstein_sq (n : ℕ) (a : cohomology Q[1] n) :
    cupBockstein C d hd_nat hd_reg k ιC (n + 1) (cupBockstein C d hd_nat hd_reg k ιC n a) =
      0 := by
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective Q[1] n a
  obtain ⟨x, y, hx, hxy⟩ := exists_regularCocycleLift C d hd_nat n a
  have hy := cochainDifferential_eq_zero_of_eq_mul C d hd_nat hd_reg n x y hxy
  rw [cupBockstein_class C d hd_nat hd_reg k ιC n a
    (projectCycle C d hd_nat (n + 1) y hy) x y hx rfl hxy]
  rw [cupBockstein_class C d hd_nat hd_reg k ιC (n + 1)
    (projectCycle C d hd_nat (n + 1) y hy) 0 y 0 rfl (map_zero _) (by rw [hy, mul_zero])]
  exact map_zero _

/-- 概要：加群のホモロジー上の Bockstein の平方は零。
方針：余鎖の持ち上げによる計算を、台加法群との同型で移す。
規約：同じ正則元で二回割る。
使われ方：Bockstein を微分とする次数付き代数。 -/
theorem bockstein_sq (n : ℕ) :
    regularBockstein C d hd_nat hd_reg k ιC n ≫
      regularBockstein C d hd_nat hd_reg k ιC (n + 1) = 0 := by
  let E := cohomologyEquivModuleHomology k Q[1] (ιC ≫ q[1])
  ext a
  obtain ⟨b, rfl⟩ := (E n).surjective a
  have h := congrArg (E (n + 1 + 1)) (cupBockstein_sq C d hd_nat hd_reg k ιC n b)
  change E (n + 1 + 1) ((E (n + 1 + 1)).symm
    (regularBockstein C d hd_nat hd_reg k ιC (n + 1)
      (E (n + 1) ((E (n + 1)).symm
        (regularBockstein C d hd_nat hd_reg k ιC n (E n b)))))) = _ at h
  change regularBockstein C d hd_nat hd_reg k ιC (n + 1)
    (regularBockstein C d hd_nat hd_reg k ιC n (E n b)) = 0
  simpa only [AddEquiv.apply_symm_apply, map_zero] using h

private theorem projection_cast {m n : ℕ} (h : m = n) (x : C.obj ⦋m⦌) :
    q[1].app ⦋n⦌ (cast (congrArg (fun j => (C.obj ⦋j⦌ : Type u)) h) x) =
      cast (congrArg (fun j => (Q[1].obj ⦋j⦌ : Type u)) h) (q[1].app ⦋m⦌ x) := by
  subst n
  rfl

private theorem class_cast {m n : ℕ} (h : m = n) (a : Cocycles Q[1] m) :
    cohomologyClass Q[1] n (cast (congrArg (fun j => ↥(Cocycles Q[1] j)) h) a) =
      cast (congrArg (cohomology Q[1]) h) (cohomologyClass Q[1] m a) := by
  subst n
  rfl

private theorem cycle_val_cast {m n : ℕ} (h : m = n) (a : Cocycles Q[1] m) :
    (cast (congrArg (fun j => ↥(Cocycles Q[1] j)) h) a).1 =
      cast (congrArg (fun j => (Q[1].obj ⦋j⦌ : Type u)) h) a.1 := by
  subst n
  rfl

/-- 概要：正則元の Bockstein はコホモロジーの cup 積に関する微分。
方針：余輪体を持ち上げ、余鎖の Leibniz 則を指定元で割って代表元公式を適用する。
規約：右側の項に左の次数の符号を掛ける。
使われ方：Hodge–Tate 写像の次数付き微分代数構造。 -/
theorem bockstein_leibniz (i j : ℕ) (a : cohomology Q[1] i) (b : cohomology Q[1] j) :
    let X := Q[1]
    let β := cupBockstein C d hd_nat hd_reg k ιC
    β (i + j) (cohomologyCup X a b) =
      cast (congrArg (cohomology X) (show (i + 1) + j = (i + j) + 1 by omega))
        (cohomologyCup X (β i a) b) +
      (-1 : ℤ) ^ i • cohomologyCup X a (β j b) := by
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective Q[1] i a
  obtain ⟨b, rfl⟩ := cohomologyClass_surjective Q[1] j b
  obtain ⟨x, u, hx, hu⟩ := exists_regularCocycleLift C d hd_nat i a
  obtain ⟨y, v, hy, hv⟩ := exists_regularCocycleLift C d hd_nat j b
  let a' := projectCycle C d hd_nat (i + 1) u
    (cochainDifferential_eq_zero_of_eq_mul C d hd_nat hd_reg i x u hu)
  let b' := projectCycle C d hd_nat (j + 1) v
    (cochainDifferential_eq_zero_of_eq_mul C d hd_nat hd_reg j y v hv)
  let e : (i + 1) + j = (i + j) + 1 := by omega
  let z : C.obj ⦋i + j + 1⦌ :=
    cast (congrArg (fun n => (C.obj ⦋n⦌ : Type u)) e) (cup C u y) +
      (-1 : ℤ) ^ i • cup C x v
  let c : Cocycles Q[1] (i + j + 1) :=
    cast (congrArg (fun n => ↥(Cocycles Q[1] n)) e) (cocycleCup Q[1] a' b) +
      (-1 : ℤ) ^ i • cocycleCup Q[1] a b'
  have hc : q[1].app ⦋i + j + 1⦌ z = c.1 := by
    change (q[1].app ⦋i + j + 1⦌).hom z = _
    dsimp only [z, c]
    rw [map_add, map_zsmul]
    change q[1].app ⦋i + j + 1⦌ _ + (-1 : ℤ) ^ i • q[1].app ⦋i + j + 1⦌ _ =
      (cast (congrArg (fun n => ↥(Cocycles Q[1] n)) e) (cocycleCup Q[1] a' b)).1 +
        (-1 : ℤ) ^ i • (cocycleCup Q[1] a b').1
    erw [projection_cast C d hd_nat e, cycle_val_cast C d hd_nat e,
      cup_natural C q[1], cup_natural C q[1], hx, hy]
    rfl
  dsimp only
  rw [cohomologyCup_class, cupBockstein_class C d hd_nat hd_reg k ιC i a a' x u hx rfl hu,
    cupBockstein_class C d hd_nat hd_reg k ιC j b b' y v hy rfl hv]
  rw [cupBockstein_class C d hd_nat hd_reg k ιC (i + j) (cocycleCup Q[1] a b) c
    (cup C x y) z (by erw [cup_natural C q[1], hx, hy]; rfl) hc
    (cochainDifferential_cup_of_eq_mul C d hd_nat x y u v hu hv)]
  rw [cohomologyCup_class, cohomologyCup_class, ← class_cast C d hd_nat e]
  exact map_add _ _ _ |>.trans (congrArg _ (map_zsmul _ _ _))

/-- 概要：正則元を保つ余単体的な環射は Bockstein と可換。
方針：持ち上げた余鎖と指定元で割った微分を、環射で写す。
規約：環射の像で係数の構造射を取る。
使われ方：Čech–Alexander 模型の変更と結晶の橋。 -/
theorem bockstein_natural
    (C' : CosimplicialObject CommRingCat.{u}) (d' : ∀ n, C'.obj n)
    (hd' : ∀ {m n} (θ : m ⟶ n), C'.map θ (d' m) = d' n)
    (hr' : ∀ n, Function.Injective (fun x : C'.obj n => d' n * x))
    (g : C ⟶ C') (hg : ∀ n, g.app n (d n) = d' n) (i : ℕ) (a : cohomology Q[1] i) :
    let X := Q[1]
    let Y := quotPow C' d' hd' 1
    let q := quotPowMap C d hd_nat d' hd' g hg 1
    cohomologyMap X Y q (i + 1) (cupBockstein C d hd_nat hd_reg k ιC i a) =
      cupBockstein C' d' hd' hr' k (ιC ≫ g) i (cohomologyMap X Y q i a) := by
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective Q[1] i a
  obtain ⟨x, y, hx, hxy⟩ := exists_regularCocycleLift C d hd_nat i a
  let b := projectCycle C d hd_nat (i + 1) y
    (cochainDifferential_eq_zero_of_eq_mul C d hd_nat hd_reg i x y hxy)
  let Y := quotPow C' d' hd' 1
  let q := quotPowMap C d hd_nat d' hd' g hg 1
  have hq (n : ℕ) (z : C.obj ⦋n⦌) :
      (quotProjection C' d' hd' 1).app ⦋n⦌ (g.app ⦋n⦌ z) = q.app ⦋n⦌ (q[1].app ⦋n⦌ z) :=
    rfl
  have hdx : cochainDifferential C' i (g.app ⦋i⦌ x) = d' ⦋i + 1⦌ * g.app ⦋i + 1⦌ y := by
    rw [← cochainDifferential_natural C C' g i, hxy, map_mul, hg]
  change cohomologyMap Q[1] Y q (i + 1) (cupBockstein C d hd_nat hd_reg k ιC i
      (cohomologyClass Q[1] i a)) =
    cupBockstein C' d' hd' hr' k (ιC ≫ g) i (cohomologyMap Q[1] Y q i (cohomologyClass Q[1] i a))
  rw [cupBockstein_class C d hd_nat hd_reg k ιC i a b x y hx rfl hxy,
    cohomologyMap_class, cohomologyMap_class]
  symm
  exact cupBockstein_class C' d' hd' hr' k (ιC ≫ g) i
    (cocycleMap Q[1] Y q i a) (cocycleMap Q[1] Y q (i + 1) b)
    (g.app ⦋i⦌ x) (g.app ⦋i + 1⦌ y) (by rw [hq, hx]; rfl) (hq _ _) hdx

end Regular

end SerrePositivity.Cosimplicial
