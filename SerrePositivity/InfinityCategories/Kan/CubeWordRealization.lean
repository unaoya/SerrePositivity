module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeGeneratorWords

/-! # 全ての具体的な cubical 射の生成語による実現
概要：元の具体的な立方体の射は全て生成語の評価であり、その等号を有限表示で判定する。
方針：生成条件の帰納法で実際の語を取り出し、既存の正規形の単射性を適用する。
規約：実現は正規化された語とは主張しない。使われ方：Serre 語評価の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の生成関数を同じ頂点関数として実現する語が存在する。 -/
lemma cubeMapGenerated_exists_word {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated f) :
    ∃ w : Quiver.Path (_root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk n) (_root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk m),
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map w).val = f := by
  induction h with
  | id n => exact ⟨Quiver.Path.nil, rfl⟩
  | face b n i =>
    exact ⟨(show _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk (n + 1) from
      _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.face b n i).toPath, rfl⟩
  | degeneracy n i =>
    exact ⟨(show _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk n from
      _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.degeneracy n i).toPath, rfl⟩
  | connection n i =>
    exact ⟨(show _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk (n + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kan.CubeWordObject.mk (n + 1) from
      _root_.SerrePositivity.InfinityCategories.Kan.CubeGenerator.connection n i).toPath, rfl⟩
  | comp hf hg ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    refine ⟨p.comp q, ?_⟩
    erw [_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_comp]
    change (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map q).val ∘
      (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map p).val = _
    rw [hp, hq]
    rfl

/-- 語の評価は具体的な立方体圏の全ての射を実現する。 -/
instance cubeWordConcreteFunctor_full : _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.Full where
  map_surjective f := by
    obtain ⟨w, hw⟩ := _root_.SerrePositivity.InfinityCategories.Kan.cubeMapGenerated_exists_word f.property
    exact ⟨w, Subtype.ext hw⟩

/-- 具体的な立方体は元の同じ次元の語の端点から回収される。 -/
lemma cubeWordConcreteFunctor_obj_surjective : Function.Surjective _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.obj := by
  intro X
  exact ⟨⟨X.dimension⟩, rfl⟩

/-- 語の具体的な意味が一致することは、同じ有限 signature の等号と同値。 -/
lemma cubeWordConcreteFunctor_map_eq_iff_signature {X Y : _root_.SerrePositivity.InfinityCategories.Kan.CubeWords} (p q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map p = _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map q ↔
      _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeSignature (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map p) =
        _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeSignature (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map q) :=
  (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeSignature_eq_iff _ _).symm

/-- 語の具体的な意味が一致することは、同じ一意な有限 max 表示の等号と同値。 -/
lemma cubeWordConcreteFunctor_map_eq_iff_normalForm {X Y : _root_.SerrePositivity.InfinityCategories.Kan.CubeWords} (p q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map p = _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map q ↔
      _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map p) =
        _root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor.map q) :=
  (_root_.SerrePositivity.InfinityCategories.Kan.concreteCubeNormalForm_eq_iff _ _).symm

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_exists_word := _root_.SerrePositivity.InfinityCategories.Kan.cubeMapGenerated_exists_word

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_full (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_full := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_full

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_map_eq_iff_normalForm := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_map_eq_iff_normalForm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_map_eq_iff_signature := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_map_eq_iff_signature

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeWordConcreteFunctor_obj_surjective := _root_.SerrePositivity.InfinityCategories.Kan.cubeWordConcreteFunctor_obj_surjective
