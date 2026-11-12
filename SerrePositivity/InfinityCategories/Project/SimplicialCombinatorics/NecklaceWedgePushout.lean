module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeMaps
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # necklace の連結は実単体集合の押し出し
概要：有限 joints の連結が、終点と始点で貼る native な wedge を回収する。
方針：単体ごとの左右被覆で射を貼り、包含への制限で自然性を証明する。
規約：全高次単体と元の包含を保持。使われ方：bead wedge と enriched 合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

open CategoryTheory Limits _root_.Simplicial SSet

variable (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {K : SSet.{u}}
  (f : T.carrier.{u} ⟶ K) (g : U.carrier.{u} ⟶ K)
  (h : T.pointMap T.last ≫ f = U.pointMap U.first ≫ g)

include h in
/-- 共有頂点上の可換条件は、全次数の元の定値単体上で一致する。 -/
lemma wedge_constant_agree (n : ℕ) :
    f.app _ (T.constantSimplex T.last n) = g.app _ (U.constantSimplex U.first n) := by
  have e := ConcreteCategory.congr_hom (NatTrans.congr_app h _)
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0).constantSimplex (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0).first n)
  change f.app _ ((T.pointMap T.last).app _ _) = g.app _ ((U.pointMap U.first).app _ _) at e
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.pointMap_app] using e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_constant_agree)


/-- 元の各単体上で、左右の指定された射を貼った写像。 -/
def wedgeGlue (n : ℕ) (s : (T.wedge U).carrier.{u} _⦋n⦌) : K _⦋n⦌ :=
  if ∀ i, (s.val i).val ≤ T.vertexMax then f.app _ ((T.wedgeFst U).app _ s)
  else g.app _ ((T.wedgeSnd U).app _ s)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeGlue)


/-- 左包含への貼り合わせの制限は、指定した元の左射。 -/
lemma wedgeGlue_inl (n : ℕ) (s : T.carrier.{u} _⦋n⦌) :
    T.wedgeGlue U f g n ((T.wedgeInl U).app _ s) = f.app _ s := by
  have hs : ∀ i, (((T.wedgeInl U).app _ s).val i).val ≤ T.vertexMax := by
    intro i
    change (s.val i).val ≤ T.vertexMax
    have := (s.val i).isLt
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue, ite_eq_left hs]
  have e := ConcreteCategory.congr_hom (NatTrans.congr_app (T.wedgeInl_fst U) _) s
  exact congrArg (f.app _) e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeGlue_inl)


include h in
/-- 右包含への貼り合わせの制限は、指定した元の右射。 -/
lemma wedgeGlue_inr (n : ℕ) (s : U.carrier.{u} _⦋n⦌) :
    T.wedgeGlue U f g n ((T.wedgeInr U).app _ s) = g.app _ s := by
  classical
  by_cases hs : ∀ i, (((T.wedgeInr U).app _ s).val i).val ≤ T.vertexMax
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue, ite_eq_left hs]
    have el : (T.wedgeFst U).app _ ((T.wedgeInr U).app _ s) =
        T.constantSimplex T.last n := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      change min (T.vertexMax + (s.val i).val) T.vertexMax = T.vertexMax
      omega
    have er : s = U.constantSimplex U.first n := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      have hi := hs i
      change T.vertexMax + (s.val i).val ≤ T.vertexMax at hi
      change (s.val i).val = 0
      omega
    rw [el, er]
    exact T.wedge_constant_agree U f g h n
  · rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue, ite_eq_right hs]
    have e := ConcreteCategory.congr_hom (NatTrans.congr_app (T.wedgeInr_snd U) _) s
    exact congrArg (g.app _) e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeGlue_inr)


include h in
/-- 左右で一致する元の二つの単体的射を、連結全体へ降ろす。 -/
def wedgeDesc : (T.wedge U).carrier.{u} ⟶ K where
  app d := by
    obtain ⟨⟨n⟩⟩ := d
    exact ↾(T.wedgeGlue U f g n)
  naturality {d e} a := by
    obtain ⟨⟨n⟩⟩ := d
    obtain ⟨⟨m⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro s
    change T.wedgeGlue U f g m ((T.wedge U).carrier.map a s) =
      K.map a (T.wedgeGlue U f g n s)
    rcases T.wedge_simplex_cover U s with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have e := ConcreteCategory.congr_hom ((T.wedgeInl U).naturality a) t
      change (T.wedgeInl U).app _ (T.carrier.map a t) =
        (T.wedge U).carrier.map a ((T.wedgeInl U).app _ t) at e
      rw [← e, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue_inl, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue_inl]
      exact ConcreteCategory.congr_hom (f.naturality a) t
    · have e := ConcreteCategory.congr_hom ((T.wedgeInr U).naturality a) t
      change (T.wedgeInr U).app _ (U.carrier.map a t) =
        (T.wedge U).carrier.map a ((T.wedgeInr U).app _ t) at e
      rw [← e, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue_inr T U f g h, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue_inr T U f g h]
      exact ConcreteCategory.congr_hom (g.naturality a) t

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeDesc)


/-- 降下射は元の左射を厳密に回収する。 -/
lemma wedgeInl_desc : T.wedgeInl U ≫ T.wedgeDesc U f g h = f := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  exact T.wedgeGlue_inl U f g n

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInl_desc)


/-- 降下射は元の右射を厳密に回収する。 -/
lemma wedgeInr_desc : T.wedgeInr U ≫ T.wedgeDesc U f g h = g := by
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  exact T.wedgeGlue_inr U f g h n

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInr_desc)


/-- 元の終点と始点の一点での実単体集合の押し出し。 -/
theorem wedge_isPushout : IsPushout (T.pointMap.{u} T.last) (U.pointMap U.first)
    (T.wedgeInl U) (T.wedgeInr U) := by
  apply IsPushout.mk' (T.wedge_seam U)
  · intro K a b hl hr
    exact T.wedge_hom_ext U hl hr
  · intro K a b hab
    exact ⟨T.wedgeDesc U a b hab, T.wedgeInl_desc U a b hab, T.wedgeInr_desc U a b hab⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedge_isPushout)


/-- 元の有限 joints 模型と、実際の一点での categorical wedge との同型。 -/
def wedgePushoutIso : (T.wedge U).carrier.{u} ≅
    pushout (T.pointMap T.last) (U.pointMap U.first) :=
  (T.wedge_isPushout.{u} U).isoPushout

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgePushoutIso)


/-- wedge 同型は元の左包含を保持する。 -/
lemma wedgeInl_pushoutIso :
    T.wedgeInl U ≫ (T.wedgePushoutIso.{u} U).hom = pushout.inl _ _ :=
  (T.wedge_isPushout.{u} U).inl_isoPushout_hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInl_pushoutIso)


/-- wedge 同型は元の右包含を保持する。 -/
lemma wedgeInr_pushoutIso :
    T.wedgeInr U ≫ (T.wedgePushoutIso.{u} U).hom = pushout.inr _ _ :=
  (T.wedge_isPushout.{u} U).inr_isoPushout_hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (wedgeInr_pushoutIso)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeDesc (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeDesc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeDesc

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeGlue := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeGlue_inl := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue_inl

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeGlue_inr := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue_inr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl_desc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInl_pushoutIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInl_pushoutIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr_desc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_desc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeInr_pushoutIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeInr_pushoutIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgePushoutIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgePushoutIso := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgePushoutIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_constant_agree := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_constant_agree

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedge_isPushout := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedge_isPushout

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeDesc._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeDesc._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeGlue.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeGlue.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgePushoutIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgePushoutIso._proof_1
