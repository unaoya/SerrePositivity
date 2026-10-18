module

public import SerrePositivity.EInfinity.BarrattEccles.Basis

/-!
# 非退化単体の基底と対称群作用

概要：Berger–Fresse §1.1 の非退化置換列の作用と正規化 Moore 複体の作用を比較する。
方針：右作用を splitting を保つ射へ持ち上げ、正規化比較同型の自然性を用いる。
規約：非退化単体上の右作用を先に線形化する。
使われ方：E(n) の基底が自由な Σₙ 集合として置換されることを示す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory CategoryTheory.Idempotents
open scoped Simplicial

/-- 概要：右作用を非退化単体へ制限する（Berger–Fresse §1.1）。
方針：右乗法による非退化性の保存を部分型の条件に用いる。
規約：群作用の順序は単体集合上の右作用と同じ。
使われ方：正規化複体の基底上の置換となる。 -/
def nondegenerateRightAction (n q : ℕ) (σ : Equiv.Perm (Fin n))
    (x : (simplicial n).nonDegenerate q) : (simplicial n).nonDegenerate q :=
  ⟨(rightAction n σ).app _ x.val,
    (rightAction_mem_nonDegenerate_iff _ _ _ _).2 x.property⟩

variable (A : Type u) [CommRing A]

/-- 概要：線形化された右作用は標準 splitting を保つ（Berger–Fresse §1.1）。
方針：非退化単体への制限を自由加群化し、包含との可換性を関手で送る。
規約：台の単体加群の射は linearization による rightAction の像。
使われ方：正規化比較同型の自然性を右作用に適用する。 -/
def linearSplitAction (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    SimplicialObject.Split.mk' (linearSplitting A n) ⟶
      SimplicialObject.Split.mk' (linearSplitting A n) where
  F := (linearization A).map (rightAction n σ)
  f q := (ModuleCat.free A).map
    (uliftFunctor.map (TypeCat.ofHom (nondegenerateRightAction n q σ)))
  comm q := by
    change (uliftFunctor.{u, 0} ⋙ ModuleCat.free A).map (TypeCat.ofHom Subtype.val) ≫
      (uliftFunctor.{u, 0} ⋙ ModuleCat.free A).map ((rightAction n σ).app _) =
        (uliftFunctor.{u, 0} ⋙ ModuleCat.free A).map
          (TypeCat.ofHom (nondegenerateRightAction n q σ)) ≫
        (uliftFunctor.{u, 0} ⋙ ModuleCat.free A).map (TypeCat.ofHom Subtype.val)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl

/-- 概要：非退化鎖と Moore 複体の比較同型は splitting を保つ射について自然である（Berger–Fresse §1.1）。
方針：Karoubi 包絡での二つの自然同型を合成し、その台の鎖写像を取る。
規約：EΣₙ の線形化の自己射について述べる。
使われ方：非退化単体の作用と正規化複体の作用を比較する。 -/
lemma nondegenerateChainIso_naturality (n : ℕ)
    (Φ : SimplicialObject.Split.mk' (linearSplitting A n) ⟶
      SimplicialObject.Split.mk' (linearSplitting A n)) :
    SimplicialObject.Split.nondegComplexFunctor.map Φ ≫ (nondegenerateChainIso A n).hom =
      (nondegenerateChainIso A n).hom ≫
        (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map Φ.F := by
  let e := SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁
      (C := ModuleCat A) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (SimplicialObject.Split.forget (ModuleCat A))
      (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi (ModuleCat A))
  apply (toKaroubi _).map_injective
  simpa [e, nondegenerateChainIso, CategoryTheory.Functor.preimageIso,
    CategoryTheory.Functor.map_comp,
    SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁,
    SimplicialObject.Split.forget, SimplicialObject.Split.mk'] using e.hom.naturality Φ

/-- 概要：Moore 複体から非退化鎖への逆比較も作用と可換する（Berger–Fresse §1.1）。
方針：比較同型の自然性に逆射を合成して消去する。
規約：splitting を保つ任意の自己射を扱う。
使われ方：自由加群表示へ作用を移す。 -/
lemma nondegenerateChainIso_inv_naturality (n : ℕ)
    (Φ : SimplicialObject.Split.mk' (linearSplitting A n) ⟶
      SimplicialObject.Split.mk' (linearSplitting A n)) :
    (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map Φ.F ≫
        (nondegenerateChainIso A n).inv =
      (nondegenerateChainIso A n).inv ≫ SimplicialObject.Split.nondegComplexFunctor.map Φ := by
  apply (cancel_mono (nondegenerateChainIso A n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [nondegenerateChainIso_naturality, Iso.inv_hom_id_assoc]

/-- 概要：E(n) の自由加群表示は Σₙ 作用と可換する（Berger–Fresse §1.1）。
方針：次数延長の自然性と Moore 比較同型の自然性を合成する。
規約：右辺は非退化単体への右作用を自由加群化した射。
使われ方：基底の像を非退化単体の右作用で計算する。 -/
lemma complexFreeIso_rightAction (n q : ℕ) (σ : Equiv.Perm (Fin n)) :
    (complexRightAction A n σ).f (-(q : ℤ)) ≫ (complexFreeIso A n q).hom =
      (complexFreeIso A n q).hom ≫ (linearSplitAction A n σ).f q := by
  let Φ := linearSplitAction A n σ
  let M := (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map
    ((linearization A).map (rightAction n σ))
  change (HomologicalComplex.extendMap M ComplexShape.embeddingDownNat).f (-(q : ℤ)) ≫
      ((complexXIso A n q).hom ≫ (nondegenerateChainIso A n).inv.f q) =
    ((complexXIso A n q).hom ≫ (nondegenerateChainIso A n).inv.f q) ≫ Φ.f q
  erw [HomologicalComplex.extendMap_f M ComplexShape.embeddingDownNat (i := q) rfl]
  simp only [complexXIso, Category.assoc, Iso.inv_hom_id_assoc]
  have h := congrArg (fun f => f.f q) (nondegenerateChainIso_inv_naturality A n Φ)
  change M.f q ≫ (nondegenerateChainIso A n).inv.f q =
    (nondegenerateChainIso A n).inv.f q ≫ Φ.f q at h
  exact congrArg ((complexXIso A n q).hom ≫ ·) h

/-- 概要：基底ベクトルは自由加群表示で標準生成元に移る（Berger–Fresse §1.1）。
方針：基底を移送した線形同値とその逆写像を消去する。
規約：添字は宇宙を持ち上げた非退化単体。
使われ方：自由加群表示で基底への作用を計算する。 -/
@[simp] lemma complexFreeIso_hom_basis (n q : ℕ)
    (x : ULift.{u} ((simplicial n).nonDegenerate q)) :
    (complexFreeIso A n q).hom (complexBasis A n q x) = ModuleCat.freeMk x := by
  change (complexFreeIso A n q).toLinearEquiv
    ((complexFreeIso A n q).toLinearEquiv.symm (Finsupp.single x 1)) = _
  exact (complexFreeIso A n q).toLinearEquiv.apply_symm_apply _

/-- 概要：Σₙ 右作用は非退化単体の右作用に従って E(n) の基底を置換する（Berger–Fresse §1.1）。
方針：自由加群表示の同変性を標準生成元で評価する。
規約：右作用は添字の置換列に同時右乗法を適用する。
使われ方：Σₙ 上自由な次数ごとの基底を示す。 -/
lemma complexBasis_rightAction (n q : ℕ) (σ : Equiv.Perm (Fin n))
    (x : ULift.{u} ((simplicial n).nonDegenerate q)) :
    (complexRightAction A n σ).f (-(q : ℤ)) (complexBasis A n q x) =
      complexBasis A n q (ULift.up (nondegenerateRightAction n q σ x.down)) := by
  apply (complexFreeIso A n q).toLinearEquiv.injective
  change (complexFreeIso A n q).hom
    ((complexRightAction A n σ).f (-(q : ℤ)) (complexBasis A n q x)) =
    (complexFreeIso A n q).hom
      (complexBasis A n q (ULift.up (nondegenerateRightAction n q σ x.down)))
  have h := congrArg (fun f => f (complexBasis A n q x)) (complexFreeIso_rightAction A n q σ)
  change (complexFreeIso A n q).hom
      ((complexRightAction A n σ).f (-(q : ℤ)) (complexBasis A n q x)) =
    (linearSplitAction A n σ).f q ((complexFreeIso A n q).hom (complexBasis A n q x)) at h
  rw [complexFreeIso_hom_basis] at h
  rw [complexFreeIso_hom_basis]
  exact h.trans (ModuleCat.free_map_apply _ x)

end SerrePositivity.EInfinity.BarrattEccles
