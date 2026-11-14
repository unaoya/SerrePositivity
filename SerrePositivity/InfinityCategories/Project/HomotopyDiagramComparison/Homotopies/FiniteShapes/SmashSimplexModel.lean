module
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.SmashSimplex

/-!
概要：smash の非基点の組による表示に単体作用を入れる。
方針：基点保存写像と標準射の可換式を使って関手則を代表の組で確認する。
規約：既存の pushout による smash との比較は別途与える。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の積の構造射の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：非基点の組と基点の表示による smash の単体的集合。
方針：面と退化は二成分への作用後に基点の組を潰す。
規約：各次数の基点は none。
使われ方：smash の pushout 表示を各次数で計算する。 -/
def smashSimplexModelSSet (A B : PointedSimplicialSet.{u}) : SSet.{u} where
  obj d := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashSimplex (PointedSimplicialSet.basepointAt A d)
    (PointedSimplicialSet.basepointAt B d)
  map {d e} f := ↾_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap (PointedSimplicialSet.basepointAt A e)
    (PointedSimplicialSet.basepointAt B e) (A.right.map f) (B.right.map f)
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro s
    obtain ⟨a, b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective
      (PointedSimplicialSet.basepointAt A d) (PointedSimplicialSet.basepointAt B d) s
    change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap _ _ _ _ _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack _ _ a b
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.map_basepointAt A _)
      (PointedSimplicialSet.map_basepointAt B _)]
    simp
  map_comp {d e k} f g := by
    apply ConcreteCategory.hom_ext
    intro s
    obtain ⟨a, b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective
      (PointedSimplicialSet.basepointAt A d) (PointedSimplicialSet.basepointAt B d) s
    change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap _ _ _ _ _ = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap _ _ _ _ _)
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.map_basepointAt A _)
      (PointedSimplicialSet.map_basepointAt B _),
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.map_basepointAt A _)
      (PointedSimplicialSet.map_basepointAt B _),
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.map_basepointAt A _)
      (PointedSimplicialSet.map_basepointAt B _)]
    simp

/-- 概要：具体的な smash の表示を基点付き単体的集合として束ねる。
方針：全ての次数の none を基点にする。
規約：一つの終対象からの自然変換で全ての基点を指定する。
使われ方：pushout の普遍性による既存の smash との比較。 -/
def smashSimplexModel (A B : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (show 𝟙_ SSet ⟶ smashSimplexModelSSet A B from {
    app _ := ↾fun _ ↦ none
    naturality := by intros; rfl })

/-- 概要：具体的な smash の基点は各次数で none。
方針：基点を指定する自然変換を評価する。
規約：次数を任意に取る。
使われ方：基点保存と軸の零化の確認。 -/
lemma smashSimplexModel_basepoint (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) :
    PointedSimplicialSet.basepointAt (smashSimplexModel A B) d = none := rfl

/-- 概要：点つき積から具体的な smash 表示への標準射。
方針：各次数で基点を含む組を基点へ潰す。
規約：面・退化との可換性と基点保存をともに検証する。
使われ方：pushout の普遍性からの比較射の入力。 -/
def smashSimplexModelQuotient (A B : PointedSimplicialSet.{u}) :
    PointedObject.prod A B ⟶ smashSimplexModel A B :=
  Under.homMk {
    app d := ↾fun p ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
      (PointedSimplicialSet.basepointAt B d) p.1 p.2
    naturality := by
      intro d e f
      apply ConcreteCategory.hom_ext
      intro p
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.map_basepointAt A f)
        (PointedSimplicialSet.map_basepointAt B f) p.1 p.2).symm } (by
    ext d x
    cases x
    change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack _ _ _ _ = none
    exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mpr (Or.inl rfl))

/-- 概要：点つき零射は各次数で基点で定数となる。
方針：零射を終対象経由の射に書き直し、終対象の元の一意性を使う。
規約：基点を次数ごとの退化像として扱う。
使われ方：smash で潰す二つの軸の具体的な計算。 -/
lemma pointedZero_app (A B : PointedSimplicialSet.{u}) (d : SimplexCategoryᵒᵖ)
    (a : A.right.obj d) : (0 : A ⟶ B).right.app d a =
      PointedSimplicialSet.basepointAt B d := by
  rw [PointedObject.zero_right]
  change B.hom.app d _ = B.hom.app d PUnit.unit
  congr 1

/-- 概要：標準射は第一の軸を基点へ潰す。
方針：第二成分が基点であることを各次数で使う。
規約：零射は基点で定数となる射。
使われ方：pushout の普遍性の第一の条件。 -/
lemma smashSimplexModelQuotient_axisLeft (A B : PointedSimplicialSet.{u}) :
    PointedObject.axisLeft A B ≫ smashSimplexModelQuotient A B = 0 := by
  apply Under.UnderMorphism.ext
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro p
  change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack _ _ p ((0 : A ⟶ B).right.app d p) =
    (0 : A ⟶ smashSimplexModel A B).right.app d p
  rw [pointedZero_app, pointedZero_app]
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mpr (Or.inr rfl)

/-- 概要：標準射は第二の軸を基点へ潰す。
方針：第一成分が基点であることを各次数で使う。
規約：零射は基点で定数となる射。
使われ方：pushout の普遍性の第二の条件。 -/
lemma smashSimplexModelQuotient_axisRight (A B : PointedSimplicialSet.{u}) :
    PointedObject.axisRight A B ≫ smashSimplexModelQuotient A B = 0 := by
  apply Under.UnderMorphism.ext
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro p
  change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack _ _ ((0 : B ⟶ A).right.app d p) p =
    (0 : B ⟶ smashSimplexModel A B).right.app d p
  rw [pointedZero_app, pointedZero_app]
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mpr (Or.inl rfl)

/-- 概要：既存の smash から具体的な単体表示への比較射。
方針：両軸の零化を確認した標準射を pushout から降ろす。
規約：既存の smash の定義を取り替えない。
使われ方：smash の各次数の表示を普遍性で同定する。 -/
def smashToSimplexModel (A B : PointedSimplicialSet.{u}) :
    PointedObject.smash A B ⟶ smashSimplexModel A B :=
  PointedObject.smashDesc (smashSimplexModelQuotient A B)
    (smashSimplexModelQuotient_axisLeft A B) (smashSimplexModelQuotient_axisRight A B)

/-- 概要：比較射を積から評価すると具体的な標準射に一致する。
方針：pushout から降ろした射の定義式を使う。
規約：点つき単体的集合の射としての等式。
使われ方：各次数の計算と比較同型の検証。 -/
lemma smashToSimplexModel_quotient (A B : PointedSimplicialSet.{u}) :
    PointedObject.smashQuotient A B ≫ smashToSimplexModel A B =
      smashSimplexModelQuotient A B := PointedObject.smashQuotient_desc ..

/-- 概要：既存の smash の標準射は第一の軸を各次数で基点へ送る。
方針：点つき対象の軸の零化の等式を成分で評価する。
規約：任意の次数と第一成分を扱う。
使われ方：具体的表示から既存の smash への逆射。 -/
lemma smashQuotient_axisLeft_app (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (a : A.right.obj d) :
    (PointedObject.smashQuotient A B).right.app d
        (a, PointedSimplicialSet.basepointAt B d) =
      PointedSimplicialSet.basepointAt (PointedObject.smash A B) d := by
  have h := congrArg (fun f : A ⟶ PointedObject.smash A B ↦ f.right.app d)
    (PointedObject.axisLeft_smashQuotient A B)
  have h' := ConcreteCategory.congr_hom h a
  change (PointedObject.smashQuotient A B).right.app d
    (a, (0 : A ⟶ B).right.app d a) = (0 : A ⟶ PointedObject.smash A B).right.app d a at h'
  simpa only [pointedZero_app] using h'

/-- 概要：既存の smash の標準射は第二の軸を各次数で基点へ送る。
方針：点つき対象の軸の零化の等式を成分で評価する。
規約：任意の次数と第二成分を扱う。
使われ方：具体的表示から既存の smash への逆射。 -/
lemma smashQuotient_axisRight_app (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (b : B.right.obj d) :
    (PointedObject.smashQuotient A B).right.app d
        (PointedSimplicialSet.basepointAt A d, b) =
      PointedSimplicialSet.basepointAt (PointedObject.smash A B) d := by
  have h := congrArg (fun f : B ⟶ PointedObject.smash A B ↦ f.right.app d)
    (PointedObject.axisRight_smashQuotient A B)
  have h' := ConcreteCategory.congr_hom h b
  change (PointedObject.smashQuotient A B).right.app d
    ((0 : B ⟶ A).right.app d b, b) = (0 : B ⟶ PointedObject.smash A B).right.app d b at h'
  simpa only [pointedZero_app] using h'

/-- 概要：具体的な表示を既存の smash の単体へ戻す写像。
方針：基点は基点へ、非基点の組は pushout の標準射へ送る。
規約：まず各次数の写像として定義する。
使われ方：比較射の逆の構成。 -/
def simplexModelToSmashApp (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) : (smashSimplexModelSSet A B).obj d →
      (PointedObject.smash A B).right.obj d
  | none => PointedSimplicialSet.basepointAt (PointedObject.smash A B) d
  | some p => (PointedObject.smashQuotient A B).right.app d p.val

/-- 概要：組から表示を経由して戻すと既存の標準射に一致する。
方針：基点を含む組には軸の零化を使い、非基点の組は定義で計算する。
規約：全ての組を扱う。
使われ方：単体作用との両立と二つの比較射の逆性。 -/
lemma simplexModelToSmashApp_pack (A B : PointedSimplicialSet.{u})
    (d : SimplexCategoryᵒᵖ) (a : A.right.obj d) (b : B.right.obj d) :
    simplexModelToSmashApp A B d
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A d)
          (PointedSimplicialSet.basepointAt B d) a b) =
      (PointedObject.smashQuotient A B).right.app d (a, b) := by
  classical
  by_cases ha : a = PointedSimplicialSet.basepointAt A d
  · subst a
    simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack, simplexModelToSmashApp, smashQuotient_axisRight_app]
  · by_cases hb : b = PointedSimplicialSet.basepointAt B d
    · subst b
      simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack, simplexModelToSmashApp, smashQuotient_axisLeft_app]
    · simp [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack, simplexModelToSmashApp, ha, hb]

/-- 概要：具体的な単体表示から既存の smash への比較射。
方針：標準射に関する計算式を使って自然性を代表の組で確認する。
規約：基点の単体も同じ自然性に含める。
使われ方：pushout の smash と具体的表示との比較同型。 -/
def simplexModelToSmash (A B : PointedSimplicialSet.{u}) :
    smashSimplexModel A B ⟶ PointedObject.smash A B :=
  Under.homMk {
    app d := ↾simplexModelToSmashApp A B d
    naturality := by
      intro d e f
      apply ConcreteCategory.hom_ext
      intro s
      obtain ⟨a, b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective
        (PointedSimplicialSet.basepointAt A d) (PointedSimplicialSet.basepointAt B d) s
      change simplexModelToSmashApp A B e (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap _ _ _ _ _) =
        (PointedObject.smash A B).right.map f (simplexModelToSmashApp A B d _)
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexMap_pack _ _ (PointedSimplicialSet.map_basepointAt A f)
        (PointedSimplicialSet.map_basepointAt B f),
        simplexModelToSmashApp_pack, simplexModelToSmashApp_pack]
      have h := (PointedObject.smashQuotient A B).right.naturality f
      exact congrArg (fun k : (A.right.obj d × B.right.obj d) ⟶
        (PointedObject.smash A B).right.obj e ↦ k (a, b)) h } (by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl)

/-- 概要：表示から戻す比較射は積からの標準射を既存の標準射へ送る。
方針：全ての次数で組に対する計算式を適用する。
規約：点つき単体的集合の射としての等式。
使われ方：pushout 側の逆性の検証。 -/
lemma simplexModelToSmash_quotient (A B : PointedSimplicialSet.{u}) :
    smashSimplexModelQuotient A B ≫ simplexModelToSmash A B =
      PointedObject.smashQuotient A B := by
  apply Under.UnderMorphism.ext
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro p
  exact simplexModelToSmashApp_pack A B d p.1 p.2

/-- 概要：既存の smash と非基点の組による単体的表示との標準同型。
方針：pushout 側は標準射のエピ性、表示側は組の代表によって逆性を示す。
規約：既存の点つき smash の定義を保持した比較同型。
使われ方：BF 1978 §2、Sp の積の構造射の単射性を単体ごとに検証する。 -/
def smashSimplexModelIso (A B : PointedSimplicialSet.{u}) :
    PointedObject.smash A B ≅ smashSimplexModel A B where
  hom := smashToSimplexModel A B
  inv := simplexModelToSmash A B
  hom_inv_id := by
    apply PointedObject.smash_hom_ext
    rw [← Category.assoc, smashToSimplexModel_quotient, simplexModelToSmash_quotient,
      Category.comp_id]
  inv_hom_id := by
    apply Under.UnderMorphism.ext
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    obtain ⟨a, b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_surjective
      (PointedSimplicialSet.basepointAt A d) (PointedSimplicialSet.basepointAt B d) s
    change (smashToSimplexModel A B).right.app d (simplexModelToSmashApp A B d _) = _
    rw [simplexModelToSmashApp_pack]
    exact congrArg (fun f : PointedObject.prod A B ⟶ smashSimplexModel A B ↦
      f.right.app d (a, b)) (smashToSimplexModel_quotient A B)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
