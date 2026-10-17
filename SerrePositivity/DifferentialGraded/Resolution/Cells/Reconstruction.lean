module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.RestrictionData
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathGeneration
public import SerrePositivity.DifferentialGraded.Complexes.SphereCochainExt

/-! # cell付加からのdg関手を有限path評価で再構成する

## 概要
cell付加からのdg関手を有限path評価で再構成する。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I) {E : Type z} [DGCategory A E]

def restrictionHomCochain (G : DGFunctor A (C.Objects A D I) E) (x y : D) :
    Cochain (C.internalHom A D I x y) (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 :=
  Cochain.ofHoms (fun n => (G.map ⟨x⟩ ⟨y⟩).f n)

lemma restrictionHomCochain_path (G : DGFunctor A (C.Objects A D I) E)
    (w : List I) (x y : D) :
    (Cochain.ofHom (C.inclusion A D I w x y)).comp
      (C.restrictionHomCochain A D I G x y) (zero_add 0) =
      (C.restrictPrimitives A D I G).pathEvaluation w x y := by
  induction w generalizing x with
  | nil =>
    apply Cochain.ext₀
    intro n
    simp only [PrimitiveData.pathEvaluation_nil, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      restrictionHomCochain, Cochain.ofHoms_v]
    rfl
  | cons b w ih =>
    apply sphereMiddleCochain_ext₀ A (C.degree b)
    intro p q n hn a t
    have h := congrArg (fun v : (C.attachedHom A D I x y).X n => (G.map ⟨x⟩ ⟨y⟩).f n v)
      (C.path_inclusion_generator A D I b w x y p q (C.degree b + q) n rfl hn a t)
    rw [DGFunctor.map_forward A G (x := ⟨x⟩) (y := ⟨C.source b⟩) (z := ⟨y⟩),
      DGFunctor.map_forward A G (x := ⟨C.source b⟩) (y := ⟨C.target b⟩) (z := ⟨y⟩)] at h
    have ht := congrArg (fun f : Cochain (C.term A D I w (C.target b) y)
        (homObject A E (G.obj ⟨C.target b⟩) (G.obj ⟨y⟩)) 0 =>
      f.v q q (add_zero q) t) (ih (C.target b))
    rw [cochain_ofHom_comp_apply, restrictionHomCochain, Cochain.ofHoms_v] at ht
    have htail := congrArg (fun z : (homObject A E (G.obj ⟨C.target b⟩) (G.obj ⟨y⟩)).X q =>
      forward A
        ((G.map ⟨x⟩ ⟨C.source b⟩).f p ((C.originalHomInclusion A D I x (C.source b)).f p a))
        (forward A ((G.map ⟨C.source b⟩ ⟨C.target b⟩).f (C.degree b)
          (C.generatorElement A D I b)) z rfl) hn) ht
    let v : (C.term A D I (b :: w) x y).X n :=
      ιTensorObj (homObject A D x (C.source b))
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y) p (C.degree b + q) n hn
        (a ⊗ₜ[A] ιTensorObj (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.degree b) q (C.degree b + q) rfl
          ((singleObjXSelf (.up ℤ) (C.degree b) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))
    have he := cochain_ofHom_comp_apply (C.inclusion A D I (b :: w) x y)
      (C.restrictionHomCochain A D I G x y) (add_zero n) v
    rw [restrictionHomCochain, Cochain.ofHoms_v] at he
    have hr := (C.restrictPrimitives A D I G).pathEvaluation_cons_generator
      b w x y p q (C.degree b + q) n rfl hn a t
    exact he.trans (h.trans (htail.trans hr.symm))

lemma restrictionHomCochain_eq_internalEvaluation (G : DGFunctor A (C.Objects A D I) E)
    (x y : D) :
    C.restrictionHomCochain A D I G x y =
      (C.restrictPrimitives A D I G).internalEvaluation x y := by
  apply C.pathCochain_ext A D I x y 0
  intro w
  rw [restrictionHomCochain_path, PrimitiveData.internalEvaluation_precomp]

lemma extension_restrict (G : DGFunctor A (C.Objects A D I) E) :
    (C.restrictPrimitives A D I G).extension = G := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (C.restrictPrimitives A D I G).extension) (G := G) (fun _ => rfl)
  intro x y
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      change (C.restrictPrimitives A D I G).attachedEvaluation x y ≫
        eqToHom (by rfl) = G.map ⟨x⟩ ⟨y⟩
      rw [eqToHom_refl, Category.comp_id]
      apply HomologicalComplex.Hom.ext
      funext n
      rw [PrimitiveData.attachedEvaluation_f]
      have h := congrArg (fun f : Cochain (C.internalHom A D I x y)
          (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 => f.v n n (add_zero n))
        (C.restrictionHomCochain_eq_internalEvaluation A D I G x y).symm
      simpa only [restrictionHomCochain, Cochain.ofHoms_v] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
