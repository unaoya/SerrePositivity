module

public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.CategoryTheory.Equivalence
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-!
# Module.Left.CategoryComparison

## 概要
左加群圏・一対象環の比較と全次数自然性をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Category（旧 SerrePositivity/DifferentialGraded/Module/Category.lean） -/

/-! # Hom end による右 dg 加群圏の豊穣構造 -/

@[expose] public section Category
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- end 合成の左単位則は各対象の左単位則から従う。 -/
lemma moduleIdentity_comp (M N : RightModule A D) :
    (λ_ (moduleHom A D M N)).inv ≫ moduleIdentity A D M ▷ _ ≫
      moduleComposition A D M M N = 𝟙 _ := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, moduleComposition_π]
  change _ ≫ (moduleIdentity A D M ⊗ₘ 𝟙 _) ≫
    (moduleHomπ A D M M x ⊗ₘ moduleHomπ A D M N x) ≫ enrichedComposition _ _ _ = _
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [moduleIdentity_π, Category.id_comp]
  rw [tensorHom_def', Category.assoc]
  rw [← leftUnitor_inv_naturality_assoc, identity_comp]
  simp

/-- end 合成の右単位則は各対象の右単位則から従う。 -/
lemma moduleComp_identity (M N : RightModule A D) :
    (ρ_ (moduleHom A D M N)).inv ≫ _ ◁ moduleIdentity A D N ≫
      moduleComposition A D M N N = 𝟙 _ := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, moduleComposition_π]
  change _ ≫ (𝟙 _ ⊗ₘ moduleIdentity A D N) ≫
    (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N N x) ≫ enrichedComposition _ _ _ = _
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [moduleIdentity_π, Category.id_comp]
  rw [tensorHom_def, Category.assoc]
  rw [← rightUnitor_inv_naturality_assoc, comp_identity]
  simp

/-- end 合成の結合則は各対象の豊穣結合則から従う。 -/
lemma moduleComposition_assoc (M N P Q : RightModule A D) :
    (α_ (moduleHom A D M N) (moduleHom A D N P) (moduleHom A D P Q)).inv ≫
      moduleComposition A D M N P ▷ _ ≫ moduleComposition A D M P Q =
    _ ◁ moduleComposition A D N P Q ≫ moduleComposition A D M N Q := by
  apply moduleHom_ext
  intro x
  simp only [Category.assoc, moduleComposition_π]
  change (α_ _ _ _).inv ≫ (moduleComposition A D M N P ⊗ₘ 𝟙 _) ≫
      (moduleHomπ A D M P x ⊗ₘ moduleHomπ A D P Q x) ≫ enrichedComposition _ _ _ =
    (𝟙 _ ⊗ₘ moduleComposition A D N P Q) ≫
      (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N Q x) ≫ enrichedComposition _ _ _
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, moduleComposition_π]
  rw [← tensorHom_comp_whiskerRight_assoc
    (moduleHomπ A D M N x ⊗ₘ moduleHomπ A D N P x)
    (enrichedComposition _ _ _) (moduleHomπ A D P Q x)]
  rw [← tensorHom_comp_whiskerLeft_assoc (moduleHomπ A D M N x)
    (moduleHomπ A D N P x ⊗ₘ moduleHomπ A D P Q x) (enrichedComposition _ _ _)]
  rw [← associator_inv_naturality_assoc (moduleHomπ A D M N x)
    (moduleHomπ A D N P x) (moduleHomπ A D P Q x)]
  have he := enrichedComposition_assoc (M.obj (Opposite.op x)) (N.obj (Opposite.op x))
    (P.obj (Opposite.op x)) (Q.obj (Opposite.op x))
  have he' := congrArg (fun f => (α_ _ _ _).inv ≫ f) he
  simp only [Iso.inv_hom_id_assoc] at he'
  rw [he']

/-- 右 dg 加群圏の主モデル。Hom は全次数自然変換の end。 -/
instance moduleEnrichment : DGCategory A (RightModule A D) :=
  ofHomObjects A (RightModule A D) (moduleHom A D) (moduleIdentity A D)
    (moduleComposition A D) (moduleIdentity_comp A D) (moduleComp_identity A D)
    (moduleComposition_assoc A D)

/-- 閉次数零の右 dg 加群圏。通常の関手圏の射には置き換えない。 -/
abbrev ModuleCategory := ClosedCategory A (RightModule A D)
/-- 対象での評価は主 Hom end から Ch(A) への豊穣関手。 -/
def moduleEvaluationDG (x : D) : DGFunctor A (RightModule A D) (Complex A) where
  obj M := M.obj (Opposite.op x)
  map M N := moduleHomπ A D M N x
  map_id M := moduleIdentity_π A D M x
  map_comp M N P := moduleComposition_π A D M N P x

/-- 閉次数零加群圏での評価を既存 chain map 圏へ接続する。 -/
def moduleEvaluation (x : D) : ModuleCategory A D ⥤ Complex A :=
  (moduleEvaluationDG A D x).forget ⋙ closedToComplex A

/-- 評価関手の射は end 評価の後の既存 chain map への比較。 -/
lemma moduleEvaluation_map (x : D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleEvaluation A D x).map f =
    complexClosedHomEquiv A ((ForgetEnrichment.to (Complex A) M).obj (Opposite.op x))
      ((ForgetEnrichment.to (Complex A) N).obj (Opposite.op x))
      (ForgetEnrichment.homOf (Complex A) (C := Complex A)
        (X := (ForgetEnrichment.to (Complex A) M).obj (Opposite.op x))
        (Y := (ForgetEnrichment.to (Complex A) N).obj (Opposite.op x))
        (ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f ≫
          moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
            (ForgetEnrichment.to (Complex A) N) x)) := rfl

/-- 閉次数零射は単位複体パラメータ付きの全次数自然変換。 -/
def moduleClosedHomEquiv (M N : ModuleCategory A D) :
    (M ⟶ N) ≃ ModuleParamTrans A D (𝟙_ (Complex A))
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) :=
  moduleHomEquiv A D _ _ _
end SerrePositivity.DifferentialGraded
end

end Category

/-! ## Ring（旧 SerrePositivity/DifferentialGraded/Module/Ring.lean） -/

/-! # 一対象 dg 環 A の右加群と非有界複体 -/

@[expose] public section Ring
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A]

/-- 任意パラメータの射に対する豊穣左単位の公式。 -/
lemma identity_tensor_comp {P Q K : Complex A} (f : K ⟶ homComplex A P Q) :
    (identity P ⊗ₘ f) ≫ enrichedComposition P P Q = (λ_ K).hom ≫ f := by
  apply (cancel_epi (λ_ K).inv).1
  rw [leftUnitor_inv_comp_tensorHom_assoc, identity_comp]
  simp

/-- 任意パラメータの射に対する豊穣右単位の公式。 -/
lemma tensor_identity_comp {P Q K : Complex A} (f : K ⟶ homComplex A P Q) :
    (f ⊗ₘ identity Q) ≫ enrichedComposition P Q Q = (ρ_ K).hom ≫ f := by
  apply (cancel_epi (ρ_ K).inv).1
  rw [rightUnitor_inv_comp_tensorHom_assoc, comp_identity]
  simp

/-- A のみが作用する一対象加群の全次数自然性。 -/
lemma ringParamNaturality {P Q K : Complex A} (f : K ⟶ homComplex A P Q) :
    (β_ K (𝟙_ (Complex A))).hom ≫ (identity P ⊗ₘ f) ≫ enrichedComposition P P Q =
      (f ⊗ₘ identity Q) ≫ enrichedComposition P Q Q := by
  rw [identity_tensor_comp, tensor_identity_comp, ← Category.assoc, braiding_leftUnitor]

/-- 複体 P の一対象 A 上の右 dg 加群。作用は閉単位の chain map。 -/
abbrev ringModule (P : Complex A) : RightModule A PUnit.{1} where
  obj _ := P
  map _ _ := identity P
  map_id _ := by
    change 𝟙 _ ≫ identity P = identity P
    simp
  map_comp _ _ _ := by
    change ((β_ (𝟙_ (Complex A)) (𝟙_ (Complex A))).hom ≫
      (λ_ (𝟙_ (Complex A))).hom) ≫ identity P =
      (identity P ⊗ₘ identity P) ≫ enrichedComposition P P P
    rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id, Category.id_comp]
    simpa only [unitors_equal] using (identity_tensor_comp A (identity P)).symm

/-- 一対象右加群の作用は単位保存から一意に定まる。 -/
lemma ringModule_map (M : RightModule A PUnit.{1}) (x : PUnit.{1}ᵒᵖ) :
    M.map x x = identity (M.obj x) := by
  have h := M.toFunctor.map_id x
  change 𝟙 _ ≫ M.map x x = identity (M.obj x) at h
  simpa only [Category.id_comp] using h

/-- 一対象加群は唯一の対象での値から復元される。 -/
lemma ringModule_recover (M : RightModule A PUnit.{1}) :
    ringModule A (M.obj (op PUnit.unit)) = M := by
  rcases M with ⟨obj, map, hid, hcomp⟩
  obtain ⟨P, hp⟩ : ∃ P : Complex A, obj = fun _ => P := by
    refine ⟨obj (op PUnit.unit), ?_⟩
    funext x
    exact congrArg obj (Subsingleton.elim x (op PUnit.unit))
  subst obj
  have hm : map = fun _ _ => identity P := by
    funext x y
    have hxy : y = x := Subsingleton.elim y x
    subst y
    have h := hid x
    change 𝟙 _ ≫ map x x = identity P at h
    simpa only [Category.id_comp] using h
  subst map
  rfl

/-- 一対象環の加群対象と既存非有界複体の厳密な同値。 -/
def ringModuleObjEquiv : RightModule A PUnit.{1} ≃ Complex A where
  toFun M := M.obj (op PUnit.unit)
  invFun := ringModule A
  left_inv := ringModule_recover A
  right_inv _ := rfl

/-- 定数一対象加群の Hom end は通常の線形 Hom 複体。 -/
def ringConstantHomIso (P Q : Complex A) :
    moduleHom A PUnit.{1} (ringModule A P) (ringModule A Q) ≅ homComplex A P Q where
  hom := moduleHomπ A PUnit.{1} (ringModule A P) (ringModule A Q) PUnit.unit
  inv := (moduleHomEquiv A PUnit.{1} _ (ringModule A P) (ringModule A Q)).symm
    { app _ := 𝟙 _
      naturality _ _ := ringParamNaturality A (𝟙 _) }
  hom_inv_id := by
    apply moduleHom_ext
    intro x
    cases x
    rw [Category.assoc, moduleHomEquiv_symm_π]
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp
  inv_hom_id := by
    rw [moduleHomEquiv_symm_π]
    rfl

/-- 任意の一対象加群でも end 評価は chain iso。 -/
instance ringModuleHomπ_isIso (M N : RightModule A PUnit.{1}) :
    IsIso (moduleHomπ A PUnit.{1} M N PUnit.unit) := by
  rw [← ringModule_recover A M, ← ringModule_recover A N]
  exact Iso.isIso_hom (ringConstantHomIso A _ _)

/-- 一対象加群の全次数 Hom end と通常の Hom 複体の比較。 -/
abbrev ringModuleHomIso (M N : RightModule A PUnit.{1}) :
    moduleHom A PUnit.{1} M N ≅
      homComplex A (M.obj (op PUnit.unit)) (N.obj (op PUnit.unit)) :=
  asIso (moduleHomπ A PUnit.{1} M N PUnit.unit)

/-- 一対象加群の閉零射と通常の chain map の同値。 -/
def ringEvaluationHomEquiv (M N : ModuleCategory A PUnit.{1}) :
    (M ⟶ N) ≃ ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M ⟶
      (moduleEvaluation A PUnit.{1} PUnit.unit).obj N) :=
  (Iso.homCongr (Iso.refl (𝟙_ (Complex A)))
    (ringModuleHomIso A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N))).trans (complexClosedHomEquiv A _ _)

/-- 一対象評価の射は上の Hom 同値で計算される。 -/
lemma ringEvaluation_map {M N : ModuleCategory A PUnit.{1}} (f : M ⟶ N) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map f = ringEvaluationHomEquiv A M N f := by
  rfl

/-- 一対象環での評価は充満。 -/
instance ringEvaluation_full : (moduleEvaluation A PUnit.{1} PUnit.unit).Full where
  map_surjective {M N} := by
    rw [funext (fun f => ringEvaluation_map A f)]
    exact (ringEvaluationHomEquiv A M N).surjective

/-- 一対象環での評価は忠実。 -/
instance ringEvaluation_faithful : (moduleEvaluation A PUnit.{1} PUnit.unit).Faithful where
  map_injective := by
    intro M N f g h
    rw [ringEvaluation_map, ringEvaluation_map] at h
    exact (ringEvaluationHomEquiv A M N).injective h

/-- 一対象環での評価は全複体を与える。 -/
instance ringEvaluation_essSurj : (moduleEvaluation A PUnit.{1} PUnit.unit).EssSurj where
  mem_essImage P := ⟨ForgetEnrichment.of (Complex A) (ringModule A P), ⟨Iso.refl P⟩⟩

/-- 充満・忠実・本質的全射による評価の同値性。 -/
instance ringEvaluation_isEquivalence :
    (moduleEvaluation A PUnit.{1} PUnit.unit).IsEquivalence where

/-- 一対象 dg 環 A 上の右加群の閉零圏は通常の非有界複体圏と同値。 -/
def ringModuleEquivalence : ModuleCategory A PUnit.{1} ≌ Complex A :=
  (moduleEvaluation A PUnit.{1} PUnit.unit).asEquivalence
end SerrePositivity.DifferentialGraded
end

end Ring

/-! ## RingDGComparison（旧 SerrePositivity/DifferentialGraded/Module/RingDGComparison.lean） -/

/-! # 一対象環Aの右dg加群と主dg複体圏の実際のdg比較

既存のHom endの評価同型を逆に使い、複体から一対象dg加群への全Hom関手を構成する。
-/

@[expose] public section RingDGComparison
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A]

/-- Hom評価同型の逆は閉零単位を保つ。評価後に既存の単位保存式を使う。 -/
lemma ringConstantHomInv_identity (P : Complex A) :
    identity P ≫ (ringConstantHomIso A P P).inv = moduleIdentity A PUnit.{1} (ringModule A P) := by
  apply (cancel_mono (ringConstantHomIso A P P).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (moduleIdentity_π A PUnit.{1} (ringModule A P) PUnit.unit).symm

/-- Hom評価同型の逆は全次数の豊穣合成を保つ。評価の合成保存とtensorの逆同型を使う。 -/
lemma ringConstantHomInv_comp (P Q R : Complex A) :
    enrichedComposition P Q R ≫ (ringConstantHomIso A P R).inv =
    ((ringConstantHomIso A P Q).inv ⊗ₘ (ringConstantHomIso A Q R).inv) ≫
      moduleComposition A PUnit.{1} (ringModule A P) (ringModule A Q) (ringModule A R) := by
  apply (cancel_mono (ringConstantHomIso A P R).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change enrichedComposition P Q R =
    ((ringConstantHomIso A P Q).inv ⊗ₘ (ringConstantHomIso A Q R).inv) ≫
      moduleComposition A PUnit.{1} (ringModule A P) (ringModule A Q) (ringModule A R) ≫
      moduleHomπ A PUnit.{1} (ringModule A P) (ringModule A R) PUnit.unit
  rw [moduleComposition_π, tensorHom_comp_tensorHom_assoc]
  change enrichedComposition P Q R =
    (((ringConstantHomIso A P Q).inv ≫ (ringConstantHomIso A P Q).hom) ⊗ₘ
      ((ringConstantHomIso A Q R).inv ≫ (ringConstantHomIso A Q R).hom)) ≫
      enrichedComposition P Q R
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- 複体を一対象環の右dg加群へ送る、全Hom評価の逆による実際のdg関手。 -/
def ringConstantDG : DGFunctor A (Complex A) (RightModule A PUnit.{1}) where
  obj := ringModule A
  map P Q := (ringConstantHomIso A P Q).inv
  map_id := ringConstantHomInv_identity A
  map_comp := ringConstantHomInv_comp A

/-- 定数一対象dg加群を評価すると、全Homの射を含めて元のdg複体関手へ戻る。 -/
lemma ringConstantDG_comp_evaluation :
    DGFunctor.comp (ringConstantDG A) (moduleEvaluationDG A PUnit.{1} PUnit.unit) =
      DGFunctor.id (A := A) (Complex A) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp (ringConstantDG A) (moduleEvaluationDG A PUnit.{1} PUnit.unit))
    (G := DGFunctor.id (A := A) (Complex A)) (fun _ => rfl)
  intro P Q
  change ((ringConstantHomIso A P Q).inv ≫ (ringConstantHomIso A P Q).hom) ≫ 𝟙 _ = 𝟙 _
  exact (Category.comp_id _).trans (ringConstantHomIso A P Q).inv_hom_id

/-- 一対象dg加群はその値から厳密に復元されるので、定数dg関手のH⁰は本質的全射である。 -/
instance ringConstantDGHomotopyEssSurj : (ringConstantDG A).onHomotopy.EssSurj where
  mem_essImage X := by
    let M : RightModule A PUnit.{1} := ForgetEnrichment.to (Complex A) X.as
    refine ⟨(toHomotopy A (Complex A)).obj
      (ForgetEnrichment.of (Complex A) (M.obj (op PUnit.unit))), ⟨eqToIso ?_⟩⟩
    exact congrArg (fun N => (toHomotopy A (RightModule A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) N)) (ringModule_recover A M)

/-- 主複体圏から一対象dg加群への関手は準同値。各Hom写像は実際に同型である。 -/
lemma ringConstantDG_quasiEquivalence : QuasiEquivalence (ringConstantDG A) := by
  refine ⟨?_, inferInstance⟩
  intro P Q
  change QuasiIso (ringConstantHomIso A P Q).inv
  infer_instance

/-- 一対象加群の評価のH⁰は本質的全射。任意の複体をその定数加群から得る。 -/
instance ringEvaluationDGHomotopyEssSurj :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.EssSurj where
  mem_essImage X :=
    ⟨(toHomotopy A (RightModule A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) (ringModule A (ForgetEnrichment.to (Complex A) X.as))),
      ⟨Iso.refl _⟩⟩

/-- 一対象dg加群の評価も準同値。全Hom endの評価がchain isoである既存の証明を使う。 -/
lemma ringEvaluationDG_quasiEquivalence :
    QuasiEquivalence (moduleEvaluationDG A PUnit.{1} PUnit.unit) := by
  refine ⟨?_, inferInstance⟩
  intro M N
  change QuasiIso (moduleHomπ A PUnit.{1} M N PUnit.unit)
  infer_instance

end SerrePositivity.DifferentialGraded
end

end RingDGComparison

/-! ## RingHomotopyComparison（旧 SerrePositivity/DifferentialGraded/Module/RingHomotopyComparison.lean） -/

/-! # 一対象Aとのdg比較が誘導する実際のH⁰同値 -/

@[expose] public section RingHomotopyComparison
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

instance ringConstantDGHomotopyFull : (ringConstantDG A).onHomotopy.Full :=
  (ringConstantDG A).onHomotopy_full_of_homIso (fun P Q => by
    change IsIso (ringConstantHomIso A P Q).inv
    infer_instance)

instance ringConstantDGHomotopyFaithful : (ringConstantDG A).onHomotopy.Faithful :=
  (ringConstantDG A).onHomotopy_faithful_of_homIso (fun P Q => by
    change IsIso (ringConstantHomIso A P Q).inv
    infer_instance)

instance ringConstantDGHomotopyIsEquivalence : (ringConstantDG A).onHomotopy.IsEquivalence where

/-- 実際の定数dg関手のH⁰による同値。 -/
def ringConstantHomotopyEquivalence : HomotopyCategory A (Complex A) ≌
    HomotopyCategory A (RightModule A PUnit.{1}) :=
  (ringConstantDG A).onHomotopy.asEquivalence

instance ringEvaluationDGHomotopyFull :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.Full :=
  (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy_full_of_homIso
    (fun _ _ => by dsimp [moduleEvaluationDG]; infer_instance)

instance ringEvaluationDGHomotopyFaithful :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.Faithful :=
  (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy_faithful_of_homIso
    (fun _ _ => by dsimp [moduleEvaluationDG]; infer_instance)

instance ringEvaluationDGHomotopyIsEquivalence :
    (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.IsEquivalence where

/-- 実際の評価dg関手のH⁰による同値。 -/
def ringEvaluationHomotopyEquivalence : HomotopyCategory A (RightModule A PUnit.{1}) ≌
    HomotopyCategory A (Complex A) :=
  (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.asEquivalence

end SerrePositivity.DifferentialGraded
end

end RingHomotopyComparison

/-! ## LeftRing（旧 SerrePositivity/DifferentialGraded/Module/LeftRing.lean） -/

/-! # 一対象環A上の左dg加群 -/

@[expose] public section LeftRing
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 任意非有界複体を一対象環A上の左加群とする。 -/
abbrev ringLeftModule (P : Complex A) : LeftModule A PUnit.{1} where
  obj _ := P
  map _ _ := identity P
  map_id _ := by
    change 𝟙 _ ≫ identity P = identity P
    exact Category.id_comp _
  map_comp _ _ _ := by
    change (λ_ (𝟙_ (Complex A))).hom ≫ identity P =
      (identity P ⊗ₘ identity P) ≫ enrichedComposition P P P
    exact (identity_tensor_comp A (identity P)).symm

/-- 一対象環上の左作用も単位保存から一意に定まる。 -/
lemma ringLeftModule_map (N : LeftModule A PUnit.{1}) (x : PUnit.{1}) :
    N.map x x = identity (N.obj x) := by
  have h := N.map_id x
  change 𝟙 _ ≫ N.map x x = identity (N.obj x) at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
end

end LeftRing

/-! ## LeftCategory（旧 SerrePositivity/DifferentialGraded/Module/LeftCategory.lean） -/

/-! # 全Hom endを持つ左dg加群圏

既存の左加群対象に、Dᵒᵖ上の右加群との比較を通じて豊穣を入れる。
通常の関手圏の自然性を全次数Homの代用にしない。
-/

@[expose] public section LeftCategory
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群のHomは二重opposite表示の主Hom end。 -/
abbrev leftModuleHom (M N : LeftModule A D) : Complex A :=
  moduleHom A Dᵒᵖ M.toRightOpposite N.toRightOpposite

instance leftModuleEnrichment : DGCategory A (LeftModule A D) :=
  ofHomObjects A (LeftModule A D) (leftModuleHom A D)
    (fun M => moduleIdentity A Dᵒᵖ M.toRightOpposite)
    (fun M N P => moduleComposition A Dᵒᵖ M.toRightOpposite N.toRightOpposite P.toRightOpposite)
    (fun M N => moduleIdentity_comp A Dᵒᵖ M.toRightOpposite N.toRightOpposite)
    (fun M N => moduleComp_identity A Dᵒᵖ M.toRightOpposite N.toRightOpposite)
    (fun M N P Q => moduleComposition_assoc A Dᵒᵖ
      M.toRightOpposite N.toRightOpposite P.toRightOpposite Q.toRightOpposite)

abbrev LeftModuleCategory := ClosedCategory A (LeftModule A D)

/-- 対象比較と恒等Homからなるdg関手。 -/
def leftModuleToRightOppositeDG : DGFunctor A (LeftModule A D) (RightModule A Dᵒᵖ) where
  obj := LeftModule.toRightOpposite
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp M N P := by
    change moduleComposition A Dᵒᵖ M.toRightOpposite N.toRightOpposite P.toRightOpposite ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ moduleComposition A Dᵒᵖ
        M.toRightOpposite N.toRightOpposite P.toRightOpposite
    simp

def leftModuleToRightOpposite : LeftModuleCategory A D ⥤ ModuleCategory A Dᵒᵖ :=
  (leftModuleToRightOppositeDG A D).onClosed

/-- 主Hom endを評価する左加群のdg評価関手。 -/
def leftModuleEvaluationDG (x : D) : DGFunctor A (LeftModule A D) (Complex A) where
  obj N := N.obj x
  map M N := moduleHomπ A Dᵒᵖ M.toRightOpposite N.toRightOpposite (op x)
  map_id M := moduleIdentity_π A Dᵒᵖ M.toRightOpposite (op x)
  map_comp M N P := moduleComposition_π A Dᵒᵖ
    M.toRightOpposite N.toRightOpposite P.toRightOpposite (op x)

def leftModuleEvaluation (x : D) : LeftModuleCategory A D ⥤ Complex A :=
  (leftModuleEvaluationDG A D x).onClosed ⋙ closedToComplex A

end SerrePositivity.DifferentialGraded
end

end LeftCategory

/-! ## LeftHomElements（旧 SerrePositivity/DifferentialGraded/Module/LeftHomElements.lean） -/

/-! # 左加群の主Hom endの全次数自然性 -/

@[expose] public section LeftHomElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev leftModuleHomπ (M N : LeftModule A D) (x : D) :
    leftModuleHom A D M N ⟶ homComplex A (M.obj x) (N.obj x) :=
  moduleHomπ A Dᵒᵖ M.toRightOpposite N.toRightOpposite (op x)

/-- 任意次数qの左加群Homと次数pの作用を交換する符号。 -/
lemma leftModuleHomElement_naturality {M N : LeftModule A D} (q : ℤ)
    (t : (leftModuleHom A D M N).X q) (x y : D) (p : ℤ) (f : GradedHom A x y p) :
    ((M.map x y).f p f).comp ((leftModuleHomπ A D M N y).f q t)
      (by omega : p + q = q + p) =
    (q * p).negOnePow • (((leftModuleHomπ A D M N x).f q t).comp
      ((N.map x y).f p f) rfl) := by
  have h := moduleHomElement_naturality A Dᵒᵖ q t (op (op x)) (op (op y)) p f
  change (((𝟙 _ ≫ M.map x y).f p f).comp ((leftModuleHomπ A D M N y).f q t)
      (by omega : p + q = q + p)) =
    (q * p).negOnePow • (((leftModuleHomπ A D M N x).f q t).comp
      ((𝟙 _ ≫ N.map x y).f p f) rfl) at h
  simpa only [Category.id_comp] using h

/-- 上のcochain自然性を任意の中間次数で評価する。 -/
lemma leftModuleHomElement_action {M N : LeftModule A D} {q p r s k n : ℤ}
    (t : (leftModuleHom A D M N).X q) (x y : D) (f : GradedHom A x y p)
    (m : (M.obj x).X r) (hs : r + p = s) (hk : r + q = k) (hn : s + q = n) :
    (((leftModuleHomπ A D M N y).f q t).v s n hn) (leftAction A M f m hs) =
    (q * p).negOnePow • leftAction A N f
      ((((leftModuleHomπ A D M N x).f q t).v r k hk) m) (by omega) := by
  have h := Cochain.congr_v (leftModuleHomElement_naturality A D q t x y p f)
    r n (by omega)
  rw [Cochain.comp_v _ _ _ r s n hs hn, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r k n hk (by omega)] at h
  exact congrArg (fun l => l m) h

end SerrePositivity.DifferentialGraded
end

end LeftHomElements

/-! ## LeftEquivalence（旧 SerrePositivity/DifferentialGraded/Module/LeftEquivalence.lean） -/

/-! # 左加群閉零圏とopposite上の右加群閉零圏の同値 -/

@[expose] public section LeftEquivalence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存比較のHom写像は主Hom end上の恒等写像。 -/
def leftModuleToRightOppositeFullyFaithful : (leftModuleToRightOpposite A D).FullyFaithful where
  preimage f := f
  map_preimage {X Y} f := by
    let H : Complex A := leftModuleHom A D (ForgetEnrichment.to (Complex A) X)
      (ForgetEnrichment.to (Complex A) Y)
    change ForgetEnrichment.homTo (Complex A) (C := RightModule A Dᵒᵖ) f ≫ 𝟙 H =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A Dᵒᵖ) f
    exact Category.comp_id _
  preimage_map {X Y} f := by
    let H : Complex A := leftModuleHom A D (ForgetEnrichment.to (Complex A) X)
      (ForgetEnrichment.to (Complex A) Y)
    change ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f ≫ 𝟙 H =
      ForgetEnrichment.homTo (Complex A) (C := LeftModule A D) f
    exact Category.comp_id _

instance leftModuleToRightOppositeEssSurj : (leftModuleToRightOpposite A D).EssSurj where
  mem_essImage R := by
    refine ⟨ForgetEnrichment.of (Complex A)
      (LeftModule.ofRightOpposite (ForgetEnrichment.to (Complex A) R)), ⟨?_⟩⟩
    exact eqToIso (congrArg (ForgetEnrichment.of (Complex A))
      (LeftModule.to_ofRightOpposite (ForgetEnrichment.to (Complex A) R)))

instance leftModuleToRightOppositeIsEquivalence :
    (leftModuleToRightOpposite A D).IsEquivalence where
  faithful := (leftModuleToRightOppositeFullyFaithful A D).faithful
  full := (leftModuleToRightOppositeFullyFaithful A D).full

/-- 対象データだけでなく、全Hom endの閉零射を持つ圏の同値。 -/
def leftRightOppositeEquivalence : LeftModuleCategory A D ≌ ModuleCategory A Dᵒᵖ :=
  (leftModuleToRightOpposite A D).asEquivalence

@[simp]
lemma leftModuleToRightOpposite_map_eval {N N' : LeftModuleCategory A D} (f : N ⟶ N') (x : D) :
    (moduleEvaluation A Dᵒᵖ (op x)).map ((leftModuleToRightOpposite A D).map f) =
      (leftModuleEvaluation A D x).map f := by
  change mapFromUnit A _ _ ((ForgetEnrichment.homTo (Complex A) f ≫ 𝟙 _) ≫
      moduleHomπ A Dᵒᵖ (ForgetEnrichment.to (Complex A) N).toRightOpposite
        (ForgetEnrichment.to (Complex A) N').toRightOpposite (op x)) =
    mapFromUnit A _ _ (ForgetEnrichment.homTo (Complex A) f ≫
      moduleHomπ A Dᵒᵖ (ForgetEnrichment.to (Complex A) N).toRightOpposite
        (ForgetEnrichment.to (Complex A) N').toRightOpposite (op x))
  rw [Category.comp_id]

end SerrePositivity.DifferentialGraded
end

end LeftEquivalence

/-! ## LeftParamNaturality（旧 SerrePositivity/DifferentialGraded/Module/LeftParamNaturality.lean） -/

/-! # 左加群の全次数パラメータ付き自然性の評価 -/

@[expose] public section LeftParamNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma leftParamNaturality_apply_of_sum {K : Complex A} {N N' : LeftModule A D}
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _)
    {x y : D} {k p r s l n : ℤ} (t : K.X k) (f : GradedHom A x y p)
    (m : (N.obj x).X r) (hs : r + p = s) (hl : r + k = l) (hn : s + k = n) :
    ((a y).f k t).v s n hn (leftAction A N f m hs) =
      (k * p).negOnePow • leftAction A N' f (((a x).f k t).v r l hl m) (by omega) := by
  let ar : ∀ x : Dᵒᵖᵒᵖ, K ⟶ homComplex A (N.obj x.unop.unop) (N'.obj x.unop.unop) :=
    fun x => a x.unop.unop
  have har : ∀ x y : Dᵒᵖᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.toRightOpposite.map x y ⊗ₘ ar y) ≫ enrichedComposition _ _ _ =
        (ar x ⊗ₘ N'.toRightOpposite.map x y) ≫ enrichedComposition _ _ _ := by
    intro x y
    change (β_ K (x.unop.unop ⟶[Complex A] y.unop.unop)).hom ≫
        ((𝟙 _ ≫ N.map x.unop.unop y.unop.unop) ⊗ₘ a y.unop.unop) ≫
          enrichedComposition _ _ _ =
      (a x.unop.unop ⊗ₘ (𝟙 _ ≫ N'.map x.unop.unop y.unop.unop)) ≫
        enrichedComposition _ _ _
    simpa only [Category.id_comp, leftAction] using ha x.unop.unop y.unop.unop
  have h := moduleParamNaturality_apply_of_sum A
    (M := N.toRightOpposite) (N := N'.toRightOpposite) ar har (m := k + p) (n := n) t
    (x := op (op x)) (y := op (op y)) f m rfl (by omega) hs hl
  change ((a y).f k t).v s n hn
      (((𝟙 _ ≫ N.map x y).f p f).v r s hs m) =
    (k * p).negOnePow • (((𝟙 _ ≫ N'.map x y).f p f).v l n (by omega)
      (((a x).f k t).v r l hl m)) at h
  simpa only [Category.id_comp, leftAction] using h

variable (D) [Small.{u} D]

/-- 左加群の主Hom評価族の全豊穣自然性。 -/
lemma leftModuleHomπ_naturality (N N' : LeftModule A D) (x y : D) :
    (β_ (leftModuleHom A D N N') (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ leftModuleHomπ A D N N' y) ≫ enrichedComposition _ _ _ =
    (leftModuleHomπ A D N N' x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _ := by
  have h := moduleHomπ_naturality A Dᵒᵖ N.toRightOpposite N'.toRightOpposite
    (op (op x)) (op (op y))
  change (β_ (leftModuleHom A D N N') (x ⟶[Complex A] y)).hom ≫
      ((𝟙 _ ≫ N.map x y) ⊗ₘ leftModuleHomπ A D N N' y) ≫ enrichedComposition _ _ _ =
    (leftModuleHomπ A D N N' x ⊗ₘ (𝟙 _ ≫ N'.map x y)) ≫ enrichedComposition _ _ _ at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
end

end LeftParamNaturality
