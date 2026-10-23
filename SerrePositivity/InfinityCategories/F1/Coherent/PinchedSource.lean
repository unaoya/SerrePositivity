module

public import SerrePositivity.InfinityCategories.F1.Coherent.PinchedEvaluation

/-!
概要：右 pinched 単体の固定面上の Hom の作用を計算する。
方針：等しい豊穣関手の Hom を対象の等号で正規化し、前半の path を先頭面から持ち上げる。
規約：対象の等号による移送を明示する。
使われ方：Kerodon Proposition 4.6.7.16、旗による評価の単体的な自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：等しい豊穣関手の Hom の作用は対象の等号で移送すると等しい。
方針：豊穣関手の等号を消去する。
規約：標的の Hom は単体集合の豊穣 Hom。
使われ方：Kerodon §2.4.3、固定面の作用の正規化。 -/
lemma enrichedFunctor_map_eqToHom_of_eq {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} C]
    {F G : EnrichedFunctor SSet.{u} A C} (h : F = G) (i j : A) :
    F.map i j ≫ eqToHom (congrArg₂ (fun a b : C ↦ (a ⟶[SSet.{u}] b))
      (congrArg (fun H ↦ H.obj i) h) (congrArg (fun H ↦ H.obj j) h)) = G.map i j := by
  subst G
  simp

/-- 概要：先頭面から入れた Hom 上で右 pinched 単体の作用は豊穣恒等に定値。
方針：固定面の豊穣関手の等号を Hom 上で評価して正規化する。
規約：任意の先頭面の二頂点に適用する。
使われ方：Kerodon Proposition 4.6.7.16、前半の path の評価の消去。 -/
lemma coherentPinched_sourceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (i j : Fin (n + 1)) :
    (SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      τ.val.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentPinched_sourceObj τ i) (coherentPinched_sourceObj τ j)) =
      toUnit _ ≫ eId SSet X := by
  have h := enrichedFunctor_map_eqToHom_of_eq τ.source
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩
  rw [coherentNerveConstant_map] at h
  change ((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      τ.val.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩) ≫ _ = _ at h
  simpa only [Category.assoc] using h

/-- 概要：旗の前半の path を先頭面の小さい順序集合内に作る。
方針：追加した最後の頂点を使わず、切断点以下の元を取る。
規約：終点は最初に選んだ段の最大元。
使われ方：Kerodon Proposition 4.6.7.16、固定面上で前半を評価するための持ち上げ。 -/
def CoherentResolutionFlag.prefixSmallPath {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (i : Fin (e + 1)) :
    Path (ULift.up F.start : ULift.{u} (Fin (n + 1))) (ULift.up (F.maxAt (α 0))) where
  I := {k | k.down ∈ F.sets (α i) ∧ k.down ≤ F.maxAt (α 0)}
  left := ⟨F.start_mem _, F.lower _ _ (F.maxAt_mem _)⟩
  right := ⟨F.monotone_sets (α.monotone (Fin.zero_le i)) (F.maxAt_mem _), le_rfl⟩
  left_le k hk := F.lower _ _ hk.1
  le_right k hk := hk.2

/-- 概要：先頭面の中の前半の path を一つの単体にする。
方針：固定した切断点以下の部分集合の包含を使う。
規約：元の先頭面の豊穣 Hom の nerve に属する単体。
使われ方：Kerodon Proposition 4.6.7.16、固定面の Hom の計算への入力。 -/
def CoherentResolutionFlag.prefixSmallFlag {n d e : ℕ} (F : CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) :
    Fin (e + 1) ⥤ Path (ULift.up F.start : ULift.{u} (Fin (n + 1)))
      (ULift.up (F.maxAt (α 0))) where
  obj i := F.prefixSmallPath α i
  map {i j} f := ⟨⟨⟨by
    intro k hk
    exact ⟨F.monotone_sets (α.monotone f.le) hk.1, hk.2⟩⟩⟩⟩

/-- 概要：先頭面に入れた小さい前半の path は元の前半の path。
方針：castSucc による集合の直接像の元を比較する。
規約：始点と終点は定義的に一致する。
使われ方：Kerodon Proposition 4.6.7.16、固定面の計算と大きい path の分解の接続。 -/
lemma CoherentResolutionFlag.front_prefixSmallPath {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1))
    (i : Fin (e + 1)) :
    (SimplicialThickening.functorMap (PinchedHom.front n).toOrderHom.uliftMap
      (⟨ULift.up F.start⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up (F.maxAt (α 0))⟩).obj (F.prefixSmallPath α i) = F.prefixPath α i := by
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro k
  change (∃ l : ULift.{u} (Fin (n + 1)), (l.down ∈ F.sets (α i) ∧ l.down ≤ F.maxAt (α 0)) ∧
      ULift.up l.down.castSucc = k) ↔
      ∃ j ∈ F.sets (α i), j ≤ F.maxAt (α 0) ∧ k.down = j.castSucc
  constructor
  · rintro ⟨l, ⟨hl, ht⟩, rfl⟩
    exact ⟨l.down, hl, ht, rfl⟩
  · rintro ⟨j, hj, ht, hk⟩
    refine ⟨ULift.up j, ⟨hj, ht⟩, ?_⟩
    exact ULift.ext hk.symm

/-- 概要：先頭面の Hom の作用は小さい前半の旗を大きい前半の旗に写す。
方針：各対象上の path の等号を関手の等号にする。
規約：豊穣 Hom の次数 e の単体での計算。
使われ方：Kerodon Proposition 4.6.7.16、先頭面の定値性を前半の旗に適用する計算。 -/
lemma CoherentResolutionFlag.front_prefixSmallFlag {n d e : ℕ}
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    ((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
      (⟨ULift.up F.start⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up (F.maxAt (α 0))⟩).app (Opposite.op ⦋e⦌) (F.prefixSmallFlag α) =
        F.prefixFlag α := by
  apply CategoryTheory.Functor.ext (fun i ↦ F.front_prefixSmallPath α i)

/-- 概要：右 pinched 単体の前半の旗の評価は豊穣恒等の単体。
方針：前半の旗を先頭面から持ち上げ、固定面の Hom の計算を適用する。
規約：二つの始域側の対象を共通の X に正規化する。
使われ方：Kerodon Proposition 4.6.7.16、旗の評価の自然性で前半を消去する式。 -/
lemma coherentPinched_prefixFlag {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n d e : ℕ}
    (τ : PinchedHom.Simplex (coherentNerveVertex X) (coherentNerveVertex Y) n)
    (F : CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    (τ.val.map ⟨ULift.up F.start.castSucc⟩ ⟨ULift.up (F.maxAt (α 0)).castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentPinched_sourceObj τ F.start)
        (coherentPinched_sourceObj τ (F.maxAt (α 0))))).app (Opposite.op ⦋e⦌)
      (F.prefixFlag α) = (eId SSet X).app (Opposite.op ⦋e⦌) PUnit.unit := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (coherentPinched_sourceMap τ F.start (F.maxAt (α 0)))
      (Opposite.op ⦋e⦌)) (F.prefixSmallFlag α)
  change (τ.val.map _ _ ≫ eqToHom _).app (Opposite.op ⦋e⦌)
    (((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
      (⟨ULift.up F.start⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
      ⟨ULift.up (F.maxAt (α 0))⟩).app (Opposite.op ⦋e⦌) (F.prefixSmallFlag α)) = _ at h
  rw [F.front_prefixSmallFlag] at h
  exact h

end SerrePositivity.InfinityCategories
