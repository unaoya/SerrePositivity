module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPushoutComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 局所化可逆な span の pushout の比較

概要：同じ脚が単射である二つの span の間の成分ごとの局所化可逆な比較は、pushout でも可逆となる。
方針：左の頂点と始域を一度 pushout して共通の始域へ移し、固定始域の比較と左固有性を使う。
規約：Segal 1974 Lemma 1.7 の模型の不変性の補助。
使われ方：二重写像円筒の span の各成分の置換。homotopy-cartesian 性の貼り合わせは別項目。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：各成分の局所化可逆な比較と単射な同じ脚から、pushout の比較の局所化可逆性を得る。
方針：共通始域の下の pushout の比較と、単射に沿った pushout の局所化可逆性を合成する。
規約：既存のモデル圏版 Quillen/LeftProper の分解を anodyneQ の具体的な定理で実装する。
使われ方：二重写像円筒の各成分の Kan 置換への移行。
-/
@[kerodon 032R]
theorem pushoutMap_localized_isIso
    {A B D A' B' D' : SSet.{u}} (f : A ⟶ B) (g : A ⟶ D) (f' : A' ⟶ B') (g' : A' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') [Mono f] [Mono f']
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hb : IsIso (AnodyneHomotopy.anodyneQ.map b))
    (hc : IsIso (AnodyneHomotopy.anodyneQ.map c))
    (ef : f ≫ b = a ≫ f') (eg : g ≫ c = a ≫ g') :
    IsIso (AnodyneHomotopy.anodyneQ.map (pushout.map f g f' g' b c a ef eg)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let U := pushout f a
  let k : A' ⟶ U := pushout.inr f a
  let u : U ⟶ B' := pushout.desc b f' ef
  have hj : IsIso (Q.map (pushout.inl f a)) :=
    KanLocalizedLeftProper.localized_isIso a ha f (pushout.inr f a) (pushout.inl f a)
      (IsPushout.of_hasPushout f a).flip
  have hu : IsIso (Q.map u) := by
    have h : pushout.inl f a ≫ u = b := pushout.inl_desc _ _ _
    have he := congrArg Q.map h
    rw [Q.map_comp] at he
    have ht : IsIso (Q.map (pushout.inl f a) ≫ Q.map u) := he.symm ▸ hb
    exact (isIso_comp_left_iff _ _).mp ht
  have hk : Mono k := by
    exact (MorphismProperty.monomorphisms SSet.{u}).of_isPushout
      (IsPushout.of_hasPushout f a).flip inferInstance
  let v : Under.mk k ⟶ Under.mk f' := Under.homMk u (by simp [k, u])
  have : Mono (Under.mk k).hom := by change Mono k; infer_instance
  have : Mono (Under.mk f').hom := by change Mono f'; infer_instance
  let q := ((Under.pushout g').map v).right
  have hq : IsIso (Q.map q) := KanPushoutComparison.localized_isIso g' v hu
  let W := pushout k g'
  let l : B ⟶ W := pushout.inl f a ≫ pushout.inl k g'
  let m : D' ⟶ W := pushout.inr k g'
  have hw : IsPushout f (a ≫ g') l m :=
    (IsPushout.of_hasPushout f a).paste_vert (IsPushout.of_hasPushout k g')
  have hw' : IsPushout f (g ≫ c) l m := eg.symm ▸ hw
  let p : pushout f g ⟶ W :=
    pushout.desc l (c ≫ m) (hw'.w.trans (Category.assoc g c m))
  have hp : IsPushout (pushout.inr f g) c p m := by
    have houter : IsPushout (g ≫ c) f m (pushout.inl f g ≫ p) := by
      simpa only [p, pushout.inl_desc] using hw'.flip
    exact (houter.of_left (by simp only [p, pushout.inr_desc])
      (IsPushout.of_hasPushout f g).flip).flip
  have hi : Mono (pushout.inr f g) :=
    (MorphismProperty.monomorphisms SSet.{u}).of_isPushout
      (IsPushout.of_hasPushout f g).flip inferInstance
  have hpw : IsIso (Q.map p) :=
    KanLocalizedLeftProper.localized_isIso c hc (pushout.inr f g) m p hp.flip
  have he : p ≫ q = pushout.map f g f' g' b c a ef eg := by
    apply pushout.hom_ext
    · dsimp [p, l]
      simp only [pushout.inl_desc_assoc]
      have hm₁ : pushout.inl f g ≫ pushout.map f g f' g' b c a ef eg =
          b ≫ pushout.inl f' g' := pushout.inl_desc _ _ _
      rw [hm₁, Category.assoc]
      have hq₁ : pushout.inl k g' ≫ q = u ≫ pushout.inl f' g' := pushout.inl_desc _ _ _
      rw [hq₁, ← Category.assoc]
      exact congrArg (fun t => t ≫ pushout.inl f' g') (pushout.inl_desc b f' ef)
    · dsimp [p, m]
      simp only [pushout.inr_desc_assoc]
      have hm₂ : pushout.inr f g ≫ pushout.map f g f' g' b c a ef eg =
          c ≫ pushout.inr f' g' := pushout.inr_desc _ _ _
      rw [hm₂, Category.assoc]
      have hq₂ : pushout.inr k g' ≫ q = pushout.inr f' g' := pushout.inr_desc _ _ _
      rw [hq₂]
  rw [← he, Q.map_comp]
  infer_instance

end SerrePositivity.KST.Comparison
