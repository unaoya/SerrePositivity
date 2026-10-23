module

public import SerrePositivity.InfinityCategories.F1.Coherent.CollageSpecifiedExtension
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.RelativeArrowCollageLeftFibration
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationSum

/-!
概要：与えられた coherent な変換を指定両端の collage 表現へ戻す。
方針：両端固定の pointed な延長を作り全頂点を被覆する両端の和で表現条件を反映する。
規約：元の分類図式 H は厳密に保ち全空間の小ささは要求しない。
使われ方：表現空間の可縮性を介する写像空間比較の左逆の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全頂点を被覆する cartesian 制限は表現条件を反映する。
方針：底の頂点を持ち上げ fiber の標準同型で同値性を戻す。
規約：底と全空間の射を指定する。
使われ方：collage の表現条件を両端の和で検査する。 -/
lemma LeftTransportSquare.isRepresentation_of_preSquare_vertexSurjective
    {p q : Arrow SSet.{u + 1}} [LeftFibration p.hom] [LeftFibration q.hom]
    (S : LeftTransportSquare q.hom) (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right)
    (hs : Function.Surjective (f.right.app (Opposite.op ⦋0⦌)))
    (hS : (S.preSquare f).IsRepresentation) : S.IsRepresentation := by
  intro b
  obtain ⟨d, rfl⟩ := hs b
  exact (S.preSquare_pointedFiberMap_isQCatEquivalence_iff f hf d).mp (hS d)

/-- 概要：区間付き底の両端の和は全頂点を被覆する。
方針：区間の頂点を零と一に分ける。
規約：底は任意。
使われ方：両端からの表現条件の反映。 -/
lemma prismEndpointPair_vertexSurjective (B : SSet.{u}) :
    Function.Surjective ((prismEndpointPair B).app (Opposite.op ⦋0⦌)) := by
  rintro ⟨t, b⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
  fin_cases i
  · exact ⟨Sum.inl b, rfl⟩
  · exact ⟨Sum.inr b, rfl⟩

/-- 概要：coherent な変換は指定両端を保つ実際の collage 表現へ戻せる。
方針：両端固定の pointed な延長を全頂点の fiber 条件で表現へ束ねる。
規約：入力の分類図式 H を厳密に保ち小ささは仮定しない。
使われ方：復元した変換と元の変換を同じ表現空間で比較する。 -/
lemma exists_coherentCollage_representation_recovery {E F B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    (R₀ : LeftTransportRepresentation p) (R₁ : LeftTransportRepresentation q)
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = R₀.diagram)
    (h₁ : prismEndpoint 1 B ≫ H = R₁.diagram)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u})
    (hw₀ : prismEndpoint 0 E ≫ W = R₀.pointedMap)
    (hw₁ : prismEndpoint 1 E ≫ W = f ≫ R₁.pointedMap)
    (hwp : W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ H) :
    letI := relativeArrowCollageProjection_leftFibration p q f hf
    ∃ R : LeftTransportRepresentation (relativeArrowCollageProjection f q),
      R.diagram = H ∧
      joinEndpointDesc (relativeJoinInl f (𝟙 F)) (relativeJoinInr f (𝟙 F)) ≫ R.pointedMap =
        joinEndpointDesc R₀.pointedMap R₁.pointedMap := by
  have := relativeArrowCollageProjection_leftFibration p q f hf
  obtain ⟨L, hL, heq⟩ :=
    exists_coherentCollage_pointed_extension_with_endpoints p q f hf R₀ R₁ H h₁ W hw₀ hw₁ hwp
  let S : LeftTransportSquare (relativeArrowCollageProjection f q) := ⟨H, L, hL⟩
  let e := joinEndpointDesc (relativeJoinInl f (𝟙 F)) (relativeJoinInr f (𝟙 F))
  have hp := isPullback_prismEndpointPair p q (relativeArrowCollageProjection f q) _ _
    (relativeArrowCollage_inl_isPullback p q f hf) (relativeArrowCollage_inr_isPullback f q)
  have : LeftFibration (joinEndpointMap p q) :=
    ⟨leftFibrations.of_isPullback hp (LeftFibration.mem (p := relativeArrowCollageProjection f q))⟩
  let a : Arrow.mk (joinEndpointMap p q) ⟶ Arrow.mk (relativeArrowCollageProjection f q) :=
    Arrow.homMk e (prismEndpointPair B) hp.w
  have : LeftFibration (Arrow.mk (joinEndpointMap p q)).hom := by
    change LeftFibration (joinEndpointMap p q); infer_instance
  have : LeftFibration (Arrow.mk (relativeArrowCollageProjection f q)).hom := by
    change LeftFibration (relativeArrowCollageProjection f q); infer_instance
  have hs : S.preSquare a = R₀.toSquare.sum R₁.toSquare := by
    apply LeftTransportSquare.ext
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      cases x with
      | inl x =>
        exact ConcreteCategory.congr_hom (C := Type (u + 1))
          (NatTrans.congr_app h₀ n) x
      | inr x =>
        exact ConcreteCategory.congr_hom (C := Type (u + 1))
          (NatTrans.congr_app h₁ n) x
    · exact heq
  have hS : S.IsRepresentation := by
    apply S.isRepresentation_of_preSquare_vertexSurjective a hp
    · exact prismEndpointPair_vertexSurjective B
    · rw [hs]
      exact R₀.toSquare.sum_isRepresentation R₁.toSquare R₀.toSquare_isRepresentation
        R₁.toSquare_isRepresentation
  refine ⟨S.toRepresentation hS, rfl, ?_⟩
  have hm : (S.toRepresentation hS).pointedMap = L := pullback.lift_fst _ _ _
  rw [hm]
  exact heq

end SerrePositivity.InfinityCategories
