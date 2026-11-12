module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderPullbackLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.SSetPullbackColimitDescent

/-!
概要：写像円柱と係数の底変換の交換。
方針：区間付き pullback の正方形と終域の正方形を、円柱の pushout の余極限で貼る。
規約：底変換の射 h は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、具体的な底変換後の円柱と局所判定の pullback の同定。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：構造射の pullback に区間を付けた正方形は係数の底について pullback。
方針：各次数で時刻を保ち、係数を元の pullback の普遍性で持ち上げる。
規約：区間は左因子。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、円柱の pushout の円柱部分の底変換。 -/
lemma mappingCylinder_prism_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback ((Δ[1] : SSet.{u}) ◁ pullback.fst f h)
      (snd (Δ[1] : SSet.{u}) (pullback f h) ≫ pullback.snd f h)
      (snd (Δ[1] : SSet.{u}) X ≫ f) h := by
  have hw : ((Δ[1] : SSet.{u}) ◁ pullback.fst f h) ≫
      (snd (Δ[1] : SSet.{u}) X ≫ f) =
        (snd (Δ[1] : SSet.{u}) (pullback f h) ≫ pullback.snd f h) ≫ h := by
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc, pullback.condition, Category.assoc]
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app hw n, ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨s, y⟩ ⟨h₁, h₂⟩
    change (t, (pullback.fst f h).app n x) = (s, (pullback.fst f h).app n y) at h₁
    change (pullback.snd f h).app n x = (pullback.snd f h).app n y at h₂
    apply Prod.ext
    · exact congrArg (fun z : (Δ[1] : SSet.{u}).obj n × X.obj n ↦ z.1) h₁
    · exact Types.ext_of_isPullback ((IsPullback.of_hasPullback f h).app n)
        (congrArg (fun z : (Δ[1] : SSet.{u}).obj n × X.obj n ↦ z.2) h₁) h₂
  · rintro ⟨t, x⟩ z hz
    obtain ⟨y, hy₁, hy₂⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback f h).app n) x z hz
    exact ⟨⟨t, y⟩, Prod.ext rfl hy₁, hy₂⟩

/-- 概要：写像円柱の底変換の正方形は pullback。
方針：両 pushout の span の各項で pullback 性を確認し、余極限による降下を使う。
規約：上辺は既存の標準比較射、左辺は係数の射影。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、円柱から係数の pullback への持ち上げの同型性。 -/
lemma mappingCylinderPullbackMap_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap f h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection (pullback.snd f h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f) h := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X
  let e' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pullback f h)
  let f' := pullback.snd f h
  let α : span e' f' ⟶ span e f :=
    { app j := match j with
        | .zero => pullback.fst f h
        | .left => (Δ[1] : SSet.{u}) ◁ pullback.fst f h
        | .right => h
      naturality j k a := by
        change WidePushoutShape.Hom j k at a
        cases a with
        | id j => rfl
        | init j =>
          cases j with
          | left => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 1 (pullback.fst f h)
          | right => exact (pullback.condition (f := f) (g := h)).symm }
  have h₀ : e ≫ pushout.inl e f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f = f := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.id_comp]
  have h₀' : e' ≫ pushout.inl e' f' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f' = f' := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.id_comp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.sset_isPullback_of_colimits
    (IsPushout.of_hasPushout e f).cocone (IsPushout.of_hasPushout e f).isColimit
    (IsPushout.of_hasPushout e' f').cocone (IsPushout.of_hasPushout e' f').isColimit α
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap f h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f') h (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap_baseProjection f h)
  · intro j
    cases j with
    | none =>
      change (e' ≫ pushout.inl e' f') ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap f h =
        pullback.fst f h ≫ (e ≫ pushout.inl e f)
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap_inl, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
    | some j =>
      cases j with
      | left => exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap_inl f h
      | right => exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackMap_inr f h
  · intro j
    cases j with
    | none =>
      change IsPullback (pullback.fst f h)
        ((e' ≫ pushout.inl e' f') ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f')
        ((e ≫ pushout.inl e f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f) h
      rw [Category.assoc, h₀', Category.assoc, h₀]
      exact IsPullback.of_hasPullback f h
    | some j =>
      cases j with
      | left =>
        change IsPullback ((Δ[1] : SSet.{u}) ◁ pullback.fst f h)
          (pushout.inl e' f' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f')
          (pushout.inl e f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f) h
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl]
        exact mappingCylinder_prism_isPullback f h
      | right =>
        change IsPullback h (pushout.inr e' f' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f')
          (pushout.inr e f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f) h
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr]
        exact IsPullback.of_vert_isIso ⟨by simp⟩

/-- 概要：底変換した写像円柱から係数の底への pullback への標準射は同型。
方針：pullback の正方形の標準同型と両射影で一致させる。
規約：同型性は既存の標準の持ち上げそのものについて述べる。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底上の比較の pullback を具体的な円柱へ戻す。 -/
instance mappingCylinderPullbackLift_isIso {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackLift f h) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackLift f h =
      (mappingCylinderPullbackMap_isPullback f h).flip.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackLift_fst, IsPullback.isoPullback_hom_fst]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderPullbackLift_snd, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
