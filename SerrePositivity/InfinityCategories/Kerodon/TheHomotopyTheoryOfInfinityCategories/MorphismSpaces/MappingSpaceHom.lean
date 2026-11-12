module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-!
概要：pinched 写像空間の比較を非定値の関手間の h Fun の Hom へ移す。
方針：π₀ とホモトピー圏の Hom の既存の全単射を比較射の前後に置く。
規約：Fun(A,X) 自体を周囲の quasicategory として使える。定値関手には制限しない。
使われ方：写像空間の比較から QCatFunctorHomCorrespondence の欄を得る橋。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：pinched 写像空間の射が誘導するホモトピー圏の Hom 写像。
方針：始域の Hom を π₀ に戻し、比較射で写して Hom に戻す。
規約：比較射の同値性は不要。
使われ方：写像空間の自然性を二胞体レベルで表示する。 -/
noncomputable def mappingSpaceHomMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁)
    (α : (HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶ HomotopyCategory.mk x₁) :
    (HomotopyCategory.mk y₀ : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y₁ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv y₀ y₁ (SSet.mapπ₀ q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x₀ x₁).symm α))

/-- 概要：写像空間のホモトピー同値は Hom 上の全単射を与える。
方針：π₀ 上の全単射と両端の Hom 表示の全単射を合成する。
規約：任意の周囲の quasicategory。
使われ方：非定値の関手間の Hom 対応の全単射性。 -/
lemma mappingSpaceHomMap_bijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence q) :
    Function.Bijective (mappingSpaceHomMap q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv y₀ y₁).bijective.comp
    (hq.mapPiZero_bijective.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x₀ x₁).symm.bijective)

/-- 概要：写像空間の指定ホモトピー同値が与える Hom の全単射。
方針：比較射の Hom 写像の全単射性から逆を取る。
規約：順方向は mappingSpaceHomMap。
使われ方：h Fun の自然な Hom 対応のデータ。 -/
noncomputable def mappingSpaceHomEquiv {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence q) :
    ((HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶ HomotopyCategory.mk x₁) ≃
      ((HomotopyCategory.mk y₀ : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y₁) :=
  Equiv.ofBijective (mappingSpaceHomMap q) (mappingSpaceHomMap_bijective q hq)

/-- 概要：代表辺の類は比較射による頂点の像の辺の類へ写る。
方針：π₀ の代表の計算則と両端の全単射の逆則を使う。
規約：s は始域の写像空間の零単体。
使われ方：比較写像の具体的な二胞体の作用の計算。 -/
lemma mappingSpaceHomMap_homMk {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁) _⦋0⦌) :
    mappingSpaceHomMap q (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x₀ x₁ s)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv y₀ y₁ (q.app (Opposite.op ⦋0⦌) s)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x₀ x₁ (SSet.π₀.mk s) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x₀ x₁ s) := rfl
  rw [← h]
  unfold mappingSpaceHomMap
  rw [Equiv.symm_apply_apply, SSet.mapπ₀_mk]
  rfl

/-- 概要：比較射の Hom への作用は全ての代表辺での値から決まる。
方針：quasicategory の任意の Hom を辺で表し、pinched の零単体へ戻す。
規約：候補 f は任意の集合の写像。同値性を仮定しない。
使われ方：指定単位の公式と写像空間比較の具体的な作用を照合する。 -/
lemma mappingSpaceHomMap_eq_of_homMk {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁)
    (f : ((HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶ HomotopyCategory.mk x₁) →
      ((HomotopyCategory.mk y₀ : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y₁))
    (hf : ∀ s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁) _⦋0⦌,
      f (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x₀ x₁ s)) =
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv y₀ y₁ (q.app (Opposite.op ⦋0⦌) s))) :
    f = mappingSpaceHomMap q := by
  funext α
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x₀ x₁ α
  have h := (hf ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x₀ x₁).symm e)).trans
    (mappingSpaceHomMap_homMk q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x₀ x₁).symm e)).symm
  simpa only [Equiv.apply_symm_apply] using h

/-- 概要：ホモトピックな写像空間比較は同じ Hom 写像を誘導する。
方針：π₀ 上のホモトピー不変性を使う。
規約：逆射の選択は入力しない。
使われ方：模型の選択と自然性ホモトピーを二胞体の等式にする。 -/
lemma mappingSpaceHomMap_eq_of_homotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    {q q' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁} (H : SSet.Homotopy q q') :
    mappingSpaceHomMap q = mappingSpaceHomMap q' := by
  funext α
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv y₀ y₁)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mapPiZero_eq_of_homotopy H ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x₀ x₁).symm α))

/-- 概要：関手の標準的な写像空間作用はホモトピー圏の関手の作用を誘導する。
方針：π₀ と Hom の比較の既存の自然性を使う。
規約：F は任意の関手。
使われ方：内部 Hom の前後合成との整合の計算。 -/
lemma mappingSpaceHomMap_functor {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (F : X ⟶ Y) (x y : X _⦋0⦌)
    (α : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    mappingSpaceHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y) α = (hoFunctor.map F).toFunctor.map α := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPiZeroToHom_naturality F x y ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x y).symm α)
  change mappingSpaceHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y) α =
    (hoFunctor.map F).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x y ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv x y).symm α)) at h
  simpa only [Equiv.apply_symm_apply] using h

/-- 概要：写像空間比較の Hom への移送は合成を保つ。
方針：中間の π₀ 表示の両逆と π₀ の関手性を使う。
規約：同値性は不要。
使われ方：自然性の正方形を Hom の等式へ移す。 -/
lemma mappingSpaceHomMap_comp {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌} {z₀ z₁ : Z _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z₀ z₁)
    (α : (HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶ HomotopyCategory.mk x₁) :
    mappingSpaceHomMap (q ≫ r) α = mappingSpaceHomMap r (mappingSpaceHomMap q α) := by
  simp only [mappingSpaceHomMap, SSet.mapπ₀_comp_apply, Equiv.symm_apply_apply]

/-- 概要：写像空間の恒等比較は Hom の恒等写像に移る。
方針：π₀ の恒等則と表示の両逆を使う。
規約：任意の quasicategory。
使われ方：比較の移送の単位則。 -/
lemma mappingSpaceHomMap_id {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌)
    (α : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    mappingSpaceHomMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)) α = α := by
  simp only [mappingSpaceHomMap, SSet.mapπ₀_id_apply, Equiv.apply_symm_apply]

/-- 概要：写像空間のホモトピー可換正方形は Hom の可換正方形に移る。
方針：比較の合成則とホモトピー不変性を合わせる。
規約：四つの周囲の quasicategory は異なってよい。
使われ方：非定値の関手間 Hom 対応の自然性を導く。 -/
lemma mappingSpaceHomMap_square {X Y X' Y' : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory X'] [Quasicategory Y']
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌} {x'₀ x'₁ : X' _⦋0⦌} {y'₀ y'₁ : Y' _⦋0⦌}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁)
    (q' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x'₀ x'₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y'₀ y'₁)
    (i : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x'₀ x'₁)
    (j : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y'₀ y'₁)
    (H : SSet.Homotopy (q ≫ j) (i ≫ q'))
    (α : (HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶ HomotopyCategory.mk x₁) :
    mappingSpaceHomMap j (mappingSpaceHomMap q α) =
      mappingSpaceHomMap q' (mappingSpaceHomMap i α) := by
  rw [← mappingSpaceHomMap_comp, ← mappingSpaceHomMap_comp,
    mappingSpaceHomMap_eq_of_homotopy H]

/-- 概要：Fun(A,Y) と Fun(A,X) の写像空間の同値は非定値関手間の Hom 全単射を与える。
方針：一般の mappingSpaceHomEquiv を二つの関手単体集合に適用する。
規約：パラメータ A の quasicategory 性は不要。U,V は任意。
使われ方：非定値 U,V の Hom 対応を構成する欄の型。 -/
noncomputable def functorMappingSpaceHomEquiv {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (U : A ⟶ X) (V : A ⟶ Y)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (U ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ G)))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence q) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ G) :=
  mappingSpaceHomEquiv q hq

/-- 概要：非定値関手間の写像空間比較のパラメータ自然性は Hom 対応の自然性を与える。
方針：前合成の pinched 写像空間作用とのホモトピー正方形を Hom へ移す。
規約：A,B の quasicategory 性は不要。比較の同値性は全単射のためにだけ使う。
使われ方：QCatFunctorHomCorrespondence の precomp 欄への接続。 -/
lemma functorMappingSpaceHomEquiv_precomp {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (i : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y)
    (qB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (U ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ G)))
    (qA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((i ≫ U) ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ V)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ U)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((i ≫ V) ≫ G)))
    (hqB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence qB) (hqA : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence qA)
    (H : SSet.Homotopy
      (qB ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre i).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ G)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre i).app Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (U ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) ≫ qA))
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ F) V) :
    functorMappingSpaceHomEquiv (i ≫ U) (i ≫ V) qA hqA
        ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) =
      (hoFunctor.map ((pre i).app X)).toFunctor.map
        (functorMappingSpaceHomEquiv U V qB hqB α) := by
  have h := mappingSpaceHomMap_square qB qA _ _ H α
  simpa only [functorMappingSpaceHomEquiv, mappingSpaceHomEquiv, Equiv.ofBijective,
    Equiv.coe_fn_mk, mappingSpaceHomMap_functor] using h.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
