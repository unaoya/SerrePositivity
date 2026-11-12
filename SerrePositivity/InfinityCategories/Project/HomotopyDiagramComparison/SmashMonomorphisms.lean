module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashProductMono

/-!
概要：点つき単体的集合の smash は単射な二射の組を単射へ送る。
方針：各次数の非基点の組による表示と標準射の全射性を使う。
規約：Kan 性やモデル構造を仮定しない。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の引き戻しの構造射の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：基点を保つ二つの単射の smash の表示への作用は単射。
方針：組の代表を取り、基点を潰す標準写像の核の等式を使う。
規約：像で基点となる元は元の基点だけであることを単射性から得る。
使われ方：smash の基礎単体写像のモノ射性の検証。 -/
lemma smashSimplexMap_injective {A B C D : Type u} {a₀ : A} {b₀ : B} {c₀ : C} {d₀ : D}
    (f : A → C) (g : B → D) (hf : f a₀ = c₀) (hg : g b₀ = d₀)
    (hi : Function.Injective f) (hj : Function.Injective g) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap (a₀ := a₀) (b₀ := b₀) c₀ d₀ f g) := by
  intro s t h
  obtain ⟨a, b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective a₀ b₀ s
  obtain ⟨a', b', rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective a₀ b₀ t
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack f g hf hg, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack f g hf hg,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff] at h
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff a₀ b₀ a a' b b').mpr
  simpa only [← hf, ← hg, hi.eq_iff, hj.eq_iff] using h

/-- 概要：単射な二つの点つき単体写像の smash は各次数で単射。
方針：組の代表を使い、具体的な smash 表示の作用の単射性へ移す。
規約：基礎単体写像のモノ射性を入力とし、Kan 性を要求しない。
使われ方：smash がモノ射を保つことの各次数の検証。 -/
lemma smashMap_app_injective {A B C D : PointedSimplicialSet.{u}}
    (f : A ⟶ C) (g : B ⟶ D) [Mono f.right] [Mono g.right] (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((PointedObject.smashMap f g).right.app d) := by
  intro s t h
  obtain ⟨⟨a, b⟩, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashQuotient_app_surjective A B d s
  obtain ⟨⟨a', b'⟩, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashQuotient_app_surjective A B d t
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_quotient_app, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_quotient_app] at h
  have h' := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel C D).right.app d z) h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient_app, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient_app] at h'
  have hi : Function.Injective (f.right.app d) :=
    (CategoryTheory.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app f.right).mp inferInstance d)
  have hj : Function.Injective (g.right.app d) :=
    (CategoryTheory.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app g.right).mp inferInstance d)
  have hs := smashSimplexMap_injective (f.right.app d) (g.right.app d)
    (PointedSimplicialSet.hom_basepointAt f d) (PointedSimplicialSet.hom_basepointAt g d) hi hj
  have he : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
      (PointedSimplicialSet.basepointAt B d) a b =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
      (PointedSimplicialSet.basepointAt B d) a' b' := by
    apply hs
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.hom_basepointAt f d)
        (PointedSimplicialSet.hom_basepointAt g d),
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.hom_basepointAt f d)
        (PointedSimplicialSet.hom_basepointAt g d)]
    exact h'
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A B d a b).symm.trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp A B d) he).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A B d a' b'))

/-- 概要：単射な二つの点つき単体写像の smash の基礎写像はモノ射。
方針：各次数の単射性を自然変換のモノ射性へ束ねる。
規約：Kan 性は不要。
使われ方：Sp の引き戻しの懸垂構造射の単射性。 -/
instance smashMap_mono {A B C D : PointedSimplicialSet.{u}}
    (f : A ⟶ C) (g : B ⟶ D) [Mono f.right] [Mono g.right] :
    Mono (PointedObject.smashMap f g).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  exact (CategoryTheory.mono_iff_injective _).mpr (smashMap_app_injective f g d)

/-- 概要：任意の点つき対象との smash による左作用は基礎モノ射を保つ。
方針：左因子の恒等射と右因子のモノ射に smash の保存を適用する。
規約：円に限らず任意の左因子を扱う。
使われ方：Sp の極限の構造射と懸垂の単射性。 -/
instance pointedWhiskerLeft_mono (A : PointedSimplicialSet.{u})
    {B C : PointedSimplicialSet.{u}} (f : B ⟶ C) [Mono f.right] : Mono (A ◁ f).right := by
  change Mono (PointedObject.smashMap (𝟙 A) f).right
  infer_instance

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
