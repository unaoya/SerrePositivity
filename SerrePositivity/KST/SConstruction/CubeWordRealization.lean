module
public import SerrePositivity.KST.SConstruction.CubeGeneratorWords

/-! # 全ての具体的な cubical 射の生成語による実現
概要：元の具体的な立方体の射は全て生成語の評価であり、その等号を有限表示で判定する。
方針：生成条件の帰納法で実際の語を取り出し、既存の正規形の単射性を適用する。
規約：実現は正規化された語とは主張しない。使われ方：Serre 語評価の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の生成関数を同じ頂点関数として実現する語が存在する。 -/
lemma cubeMapGenerated_exists_word {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (h : CubeMapGenerated f) :
    ∃ w : Quiver.Path (CubeWordObject.mk n) (CubeWordObject.mk m),
      (cubeWordConcreteFunctor.map w).val = f := by
  induction h with
  | id n => exact ⟨Quiver.Path.nil, rfl⟩
  | face b n i =>
    exact ⟨(show CubeWordObject.mk n ⟶ CubeWordObject.mk (n + 1) from
      CubeGenerator.face b n i).toPath, rfl⟩
  | degeneracy n i =>
    exact ⟨(show CubeWordObject.mk (n + 1) ⟶ CubeWordObject.mk n from
      CubeGenerator.degeneracy n i).toPath, rfl⟩
  | connection n i =>
    exact ⟨(show CubeWordObject.mk (n + 2) ⟶ CubeWordObject.mk (n + 1) from
      CubeGenerator.connection n i).toPath, rfl⟩
  | comp hf hg ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    refine ⟨p.comp q, ?_⟩
    erw [cubeWordConcreteFunctor_comp]
    change (cubeWordConcreteFunctor.map q).val ∘
      (cubeWordConcreteFunctor.map p).val = _
    rw [hp, hq]
    rfl

/-- 語の評価は具体的な立方体圏の全ての射を実現する。 -/
instance cubeWordConcreteFunctor_full : cubeWordConcreteFunctor.Full where
  map_surjective f := by
    obtain ⟨w, hw⟩ := cubeMapGenerated_exists_word f.property
    exact ⟨w, Subtype.ext hw⟩

/-- 具体的な立方体は元の同じ次元の語の端点から回収される。 -/
lemma cubeWordConcreteFunctor_obj_surjective : Function.Surjective cubeWordConcreteFunctor.obj := by
  intro X
  exact ⟨⟨X.dimension⟩, rfl⟩

/-- 語の具体的な意味が一致することは、同じ有限 signature の等号と同値。 -/
lemma cubeWordConcreteFunctor_map_eq_iff_signature {X Y : CubeWords} (p q : X ⟶ Y) :
    cubeWordConcreteFunctor.map p = cubeWordConcreteFunctor.map q ↔
      concreteCubeSignature (cubeWordConcreteFunctor.map p) =
        concreteCubeSignature (cubeWordConcreteFunctor.map q) :=
  (concreteCubeSignature_eq_iff _ _).symm

/-- 語の具体的な意味が一致することは、同じ一意な有限 max 表示の等号と同値。 -/
lemma cubeWordConcreteFunctor_map_eq_iff_normalForm {X Y : CubeWords} (p q : X ⟶ Y) :
    cubeWordConcreteFunctor.map p = cubeWordConcreteFunctor.map q ↔
      concreteCubeNormalForm (cubeWordConcreteFunctor.map p) =
        concreteCubeNormalForm (cubeWordConcreteFunctor.map q) :=
  (concreteCubeNormalForm_eq_iff _ _).symm

end SerrePositivity.KST.SConstruction
