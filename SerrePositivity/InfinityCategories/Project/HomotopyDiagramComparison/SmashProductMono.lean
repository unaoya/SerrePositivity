module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashSimplexModel

/-!
概要：smash と二項積の標準比較の単射性。
方針：具体的表示の同型で各単体を組の代表へ戻し、二射影で識別する。
規約：通常の点つき単体的集合の smash と積を使う。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の積の懸垂構造射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：点つき通常積の各次数の基点は二つの基点の組。
方針：基点保存を二つの射影に適用する。
規約：smash の基点と通常積の基点を区別する。
使われ方：具体的な smash 表示での積の基点の同定。 -/
lemma pointedProduct_basepointAt (B C : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    PointedSimplicialSet.basepointAt (PointedObject.prod B C) d =
      (PointedSimplicialSet.basepointAt B d, PointedSimplicialSet.basepointAt C d) :=
  Prod.ext (PointedSimplicialSet.hom_basepointAt (PointedObject.prodFst B C) d)
    (PointedSimplicialSet.hom_basepointAt (PointedObject.prodSnd B C) d)

/-- 概要：既存の smash の単体は積の単体の像として表せる。
方針：具体的表示への同型と組の代表の全射性を使う。
規約：次数と二つの点つき単体的集合は任意。
使われ方：smash 上の射の各次数での単射性の検証。 -/
lemma smashQuotient_app_surjective (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.Surjective ((PointedObject.smashQuotient A B).right.app d) := by
  intro s
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexModelIso A B
  obtain ⟨a, b, h⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective
    (PointedSimplicialSet.basepointAt A d) (PointedSimplicialSet.basepointAt B d)
    (e.hom.right.app d s)
  refine ⟨(a, b), ?_⟩
  have h' := congrArg (fun t ↦ e.inv.right.app d t) h
  change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp A B d _ = e.inv.right.app d (e.hom.right.app d s) at h'
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack] at h'
  have hi := congrArg (fun f : PointedObject.smash A B ⟶ PointedObject.smash A B ↦
    f.right.app d s) e.hom_inv_id
  exact h'.trans hi

/-- 概要：既存の標準射を具体的表示へ写すと組を潰す標準写像になる。
方針：比較射の標準射との可換式を各次数で評価する。
規約：基点を含む組も扱う。
使われ方：smash と二項積の比較の二射影の計算。 -/
lemma smashToSimplexModel_quotient_app (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (a : A.right.obj d) (b : B.right.obj d) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel A B).right.app d
        ((PointedObject.smashQuotient A B).right.app d (a, b)) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
        (PointedSimplicialSet.basepointAt B d) a b :=
  congrArg (fun f : PointedObject.prod A B ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexModel A B ↦
    f.right.app d (a, b)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient A B)

/-- 概要：smash の写像は組の代表への作用と可換。
方針：smashMap の標準射との可換式を各次数で評価する。
規約：任意の二つの点つき射を扱う。
使われ方：積の射影による smash の比較の計算。 -/
lemma smashMap_quotient_app {A B A' B' : PointedSimplicialSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (d : SimplexCategoryᵒᵖ)
    (a : A.right.obj d) (b : B.right.obj d) :
    (PointedObject.smashMap f g).right.app d
        ((PointedObject.smashQuotient A B).right.app d (a, b)) =
      (PointedObject.smashQuotient A' B').right.app d (f.right.app d a, g.right.app d b) :=
  congrArg (fun k : PointedObject.prod A B ⟶ PointedObject.smash A' B' ↦
    k.right.app d (a, b)) (PointedObject.smashQuotient_map f g)

/-- 概要：右因子の二射影による smash と二項積の標準比較。
方針：左因子は恒等射、右因子は積の射影として二つの smashMap を組にする。
規約：右因子の積は点つき通常積。
使われ方：Sp の積の懸垂構造射の単射性。 -/
def smashProductComparison (A B C : PointedSimplicialSet.{u}) :
    PointedObject.smash A (PointedObject.prod B C) ⟶
      PointedObject.prod (PointedObject.smash A B) (PointedObject.smash A C) :=
  PointedObject.prodLift (PointedObject.smashMap (𝟙 A) (PointedObject.prodFst B C))
    (PointedObject.smashMap (𝟙 A) (PointedObject.prodSnd B C))

/-- 概要：smash と二項積の標準比較は各次数で単射。
方針：積の組の代表を取り、二つの射影の像を具体的表示で比較する。
規約：基点の組を含めて単射性を証明し、Kan 性を仮定しない。
使われ方：BF 1978 §2、Sp の積の懸垂構造射の単射性。 -/
lemma smashProductComparison_app_injective (A B C : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((smashProductComparison A B C).right.app d) := by
  intro s t h
  obtain ⟨⟨a, b, c⟩, rfl⟩ := smashQuotient_app_surjective A (PointedObject.prod B C) d s
  obtain ⟨⟨a', b', c'⟩, rfl⟩ := smashQuotient_app_surjective A (PointedObject.prod B C) d t
  have hb := congrArg (fun z ↦ (PointedObject.prodFst
    (PointedObject.smash A B) (PointedObject.smash A C)).right.app d z) h
  have hc := congrArg (fun z ↦ (PointedObject.prodSnd
    (PointedObject.smash A B) (PointedObject.smash A C)).right.app d z) h
  change ((smashProductComparison A B C ≫ PointedObject.prodFst _ _).right.app d
    ((PointedObject.smashQuotient A (PointedObject.prod B C)).right.app d (a, b, c))) =
    ((smashProductComparison A B C ≫ PointedObject.prodFst _ _).right.app d
    ((PointedObject.smashQuotient A (PointedObject.prod B C)).right.app d (a', b', c'))) at hb
  change ((smashProductComparison A B C ≫ PointedObject.prodSnd _ _).right.app d
    ((PointedObject.smashQuotient A (PointedObject.prod B C)).right.app d (a, b, c))) =
    ((smashProductComparison A B C ≫ PointedObject.prodSnd _ _).right.app d
    ((PointedObject.smashQuotient A (PointedObject.prod B C)).right.app d (a', b', c'))) at hc
  simp only [smashProductComparison, PointedObject.prodLift_fst] at hb
  simp only [smashProductComparison, PointedObject.prodLift_snd] at hc
  rw [smashMap_quotient_app, smashMap_quotient_app] at hb hc
  have hb' := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel A B).right.app d z) hb
  have hc' := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel A C).right.app d z) hc
  rw [smashToSimplexModel_quotient_app, smashToSimplexModel_quotient_app] at hb' hc'
  have hp := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexProductComparison_injective
    (PointedSimplicialSet.basepointAt A d) (PointedSimplicialSet.basepointAt B d)
    (PointedSimplicialSet.basepointAt C d)
  have he : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
      (PointedSimplicialSet.basepointAt B d, PointedSimplicialSet.basepointAt C d) a (b, c) =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
      (PointedSimplicialSet.basepointAt B d, PointedSimplicialSet.basepointAt C d) a' (b', c') := by
    apply hp
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexProductComparison_pack, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexProductComparison_pack]
    exact Prod.ext hb' hc'
  rw [← pointedProduct_basepointAt] at he
  have he' := congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp A (PointedObject.prod B C) d) he
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A (PointedObject.prod B C) d a (b, c)).symm.trans
    (he'.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A (PointedObject.prod B C) d a' (b', c')))

/-- 概要：smash と二項積の標準比較の基礎単体写像はモノ射。
方針：各次数の単射性を自然変換のモノ射の判定で束ねる。
規約：Kan 性も構造射も仮定しない。
使われ方：Sp の二項積の構造射の単射性。 -/
instance smashProductComparison_mono (A B C : PointedSimplicialSet.{u}) :
    Mono (smashProductComparison A B C).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  exact (CategoryTheory.mono_iff_injective _).mpr (smashProductComparison_app_injective A B C d)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
