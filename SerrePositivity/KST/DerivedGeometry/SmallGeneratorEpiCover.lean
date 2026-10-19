module

public import SerrePositivity.KST.DerivedGeometry.GeneratorEpiWitness

/-!
概要：全射の終域の部分対象集合で添字付けた生成対象の直和から、小さい全射部分対象を作る。
方針：各真部分対象を経由しない射を選び、その直和の像を取る。
規約：終域の部分対象の型を小さい universe へ縮小して実際の直和を構成する。
使われ方：Stacks Lemma 19.12.1 (079J)・19.12.2、TT §3・§8、Toën §3.2 の試験集合の上界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
open scoped Classical
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G) {M N : C} (p : M ⟶ N) [Epi p]

/--
概要：各真部分対象を経由しない生成対象から全射の始域への射を選ぶ。
方針：pullback と生成性で証明済みの存在を使う。
規約：終域全体の部分対象に対しては零射を割り当てる。
使われ方：Stacks 19.12.1、TT §3 の小さい直和の構成。
-/
def generatorEpiCoverComponent (S : Subobject N) : G ⟶ M :=
  if h : S ≠ ⊤ then (exists_generator_map_not_factor G hG p S h).choose else 0

/--
概要：選んだ成分の合成は指定した真部分対象を経由しない。
方針：実際の存在証明で選んだ射の性質を使う。
規約：部分対象は縮小する前の型で指定する。
使われ方：Stacks 19.12.1、TT §3 の像の全射性。
-/
lemma generatorEpiCoverComponent_not_factor (S : Subobject N) (hS : S ≠ ⊤) :
    ¬ ∃ g : G ⟶ (S : C), g ≫ S.arrow = generatorEpiCoverComponent G hG p S ≫ p := by
  dsimp [generatorEpiCoverComponent]
  rw [dite_eq_left hS]
  exact (exists_generator_map_not_factor G hG p S hS).choose_spec

/--
概要：小さい部分対象の添字集合で表した被覆の成分。
方針：縮小の同値の逆像で元の部分対象に戻す。
規約：実際の射の選択は縮小前に行う。
使われ方：Stacks 19.12.1、TT §3 の小さい直和。
-/
def smallGeneratorEpiCoverComponent (s : Shrink.{w} (Subobject N)) : G ⟶ M :=
  generatorEpiCoverComponent G hG p ((equivShrink (Subobject N)).symm s)

/--
概要：選んだ射の直和から全射の始域への射。
方針：部分対象の小さい添字集合上の coproduct を取る。
規約：生成対象が projective であるとは仮定しない。
使われ方：Stacks 19.12.1、TT §3 の濃度の上界を持つ部分対象。
-/
def smallGeneratorEpiCoverMap :
    (∐ fun _ : Shrink.{w} (Subobject N) => G) ⟶ M :=
  Sigma.desc (smallGeneratorEpiCoverComponent G hG p)

/--
概要：選んだ射の直和と元の全射との合成は全射。
方針：その像が真部分対象なら、その部分対象で選んだ射との矛盾を得る。
規約：全射性を未証明のフィールドとして置かない。
使われ方：Stacks 19.12.1、TT §3 の小さい全射部分対象の存在。
-/
instance smallGeneratorEpiCoverMap_comp_epi : Epi (smallGeneratorEpiCoverMap G hG p ≫ p) := by
  classical
  let e := smallGeneratorEpiCoverMap G hG p
  let q := e ≫ p
  have ht : imageSubobject q = ⊤ := by
    by_contra ht
    let s := equivShrink (Subobject N) (imageSubobject q)
    have hsEq : (equivShrink (Subobject N)).symm s = imageSubobject q :=
      (equivShrink (Subobject N)).symm_apply_apply _
    have hw : ¬ ∃ g : G ⟶ (imageSubobject q : C),
        g ≫ (imageSubobject q).arrow = smallGeneratorEpiCoverComponent G hG p s ≫ p := by
      dsimp only [smallGeneratorEpiCoverComponent]
      rw [hsEq]
      exact generatorEpiCoverComponent_not_factor G hG p _ ht
    apply hw
    refine ⟨Sigma.ι (fun _ : Shrink.{w} (Subobject N) => G) s ≫
      factorThruImageSubobject q, ?_⟩
    rw [Category.assoc, imageSubobject_arrow_comp]
    change Sigma.ι _ s ≫ (e ≫ p) = _
    rw [← Category.assoc]
    change (Sigma.ι _ s ≫ Sigma.desc _) ≫ p = _
    rw [Sigma.ι_comp_desc]
  have : IsIso (imageSubobject q).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr ht
  have he : Epi q := by
    rw [← imageSubobject_arrow_comp q]
    infer_instance
  exact he

include hG

/--
概要：全射の始域に、固定された小さい生成対象の直和の商としての全射部分対象が存在する。
方針：選んだ直和の射の実際の像を取り、像分解で単射と全射を証明する。
規約：直和の添字は終域の部分対象集合の縮小。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の小さい非輪状部分複体の帰納構成。
-/
lemma exists_small_generator_epi_subobject :
    ∃ (M' : C) (a : (∐ fun _ : Shrink.{w} (Subobject N) => G) ⟶ M') (i : M' ⟶ M),
      Epi a ∧ Mono i ∧ Epi (i ≫ p) := by
  let e := smallGeneratorEpiCoverMap G hG p
  have he : Epi (factorThruImage e ≫ (image.ι e ≫ p)) := by
    rw [← Category.assoc, image.fac]
    exact smallGeneratorEpiCoverMap_comp_epi G hG p
  have : Epi (image.ι e ≫ p) := epi_of_epi (factorThruImage e) (image.ι e ≫ p)
  exact ⟨image e, factorThruImage e, image.ι e, inferInstance, inferInstance, inferInstance⟩

end SerrePositivity.KST.DerivedGeometry
