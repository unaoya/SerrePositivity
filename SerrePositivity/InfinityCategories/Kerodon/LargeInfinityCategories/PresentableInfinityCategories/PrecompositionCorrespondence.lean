module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceTransport

/-!
概要：転置と元の随伴から得る前合成の Hom 対応を端点の輸送付きで記述する。
方針：二つの転置の間に Hom₁ の逆対応を挟み、自然性を計算する。
規約：全てのパラメータと元の全関手圏の Hom を保持する。
使われ方：前合成の全 QCat 随伴と左射影の普遍単位模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomMap

/-- 概要：三つの全単射を通る対応は出口の全単射で元の対応へ戻る。
方針：出口の両逆のみを使う。
規約：全単射の内部構成を展開しない。
使われ方：大きな関手圏の端点輸送を含む対応の回収。 -/
lemma equivalenceTransfer_formula {X Y W T : Type*}
    (e₁ : X ≃ Y) (e₂ : Y ≃ T) (e₃ : W ≃ T) (x : X) :
    e₃ ((e₁.trans (e₂.trans e₃.symm)) x) = e₂ (e₁ x) :=
  e₃.apply_symm_apply _

/-- 概要：転置した Hom の始点を右関手による前合成へ正規化する。
方針：転置の全単射と端点輸送を合成する。
規約：輸送の全ての関手を明示する。
使われ方：前合成の Hom 対応の入口。 -/
def precompositionSourceEquiv {A C D Z : SSet.{u}} [Quasicategory Z]
    (R : D ⟶ C) (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (A := A) (B := D) (Z := Z) (U ≫ (pre R).app Z) V).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceHomTransportEquiv (A := D) (E := (ihom A).obj Z)
      (V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U))

/-- 概要：転置した Hom の終点を左関手による前合成へ正規化する。
方針：転置の全単射と端点輸送を合成する。
規約：輸送の全ての関手を明示する。
使われ方：前合成の Hom 対応の出口。 -/
def precompositionTargetEquiv {A C D Z : SSet.{u}} [Quasicategory Z]
    (L : C ⟶ D) (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (L ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (A := A) (B := C) (Z := Z) U (V ≫ (pre L).app Z)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := C) (D := (ihom A).obj Z)
      (U := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (V ≫ (pre L).app Z))
      (U' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (V' := L ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V)
      rfl (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V))

/-- 概要：入口の転置と輸送は標的側の合成を保つ。
方針：転置と端点輸送の合成保存を順に適用する。
規約：元の Hom と右関手を保持する。
使われ方：前合成の Hom 対応の標的自然性。 -/
lemma precompositionSourceEquiv_comp {A C D Z : SSet.{u}} [Quasicategory Z]
    (R : D ⟶ C) {U : A ⟶ (ihom C).obj Z} {V V' : A ⟶ (ihom D).obj Z}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V V') :
    precompositionSourceEquiv (Z := Z) R U V' (α ≫ β) =
      precompositionSourceEquiv (Z := Z) R U V α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := Z) V V' β := by
  exact (congrArg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceHomTransportEquiv (A := D) (E := (ihom A).obj Z)
      (V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V') (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_comp (A := A) (B := D) (Z := Z)
      (U := U ≫ (pre R).app Z) (V := V) (W := V') α β)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceHomTransportEquiv_comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U) _ _)

/-- 概要：出口の転置と輸送は標的側の前合成作用と合成を保つ。
方針：転置の合成保存と第二始域の自然性を適用する。
規約：元の左関手を保持する。
使われ方：前合成の Hom 対応の標的自然性。 -/
lemma precompositionTargetEquiv_comp {A C D Z : SSet.{u}} [Quasicategory Z]
    (L : C ⟶ D) {U : A ⟶ (ihom C).obj Z} {V V' : A ⟶ (ihom D).obj Z}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z)) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V V') :
    precompositionTargetEquiv (Z := Z) L U V' (α ≫
      (hoFunctor.map ((ihom A).map ((pre L).app Z))).toFunctor.map
        (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V))
        (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V')) β) =
    precompositionTargetEquiv (Z := Z) L U V α ≫
      (hoFunctor.map ((pre L).app ((ihom A).obj Z))).toFunctor.map
        (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V)))
        (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V')))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := Z) V V' β) := by
  let b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (V ≫ (pre L).app Z) (V' ≫ (pre L).app Z) :=
    (hoFunctor.map ((ihom A).map ((pre L).app Z))).toFunctor.map
      (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V')) β
  change precompositionTargetEquiv (Z := Z) L U V' (α ≫ b) = _
  dsimp only [precompositionTargetEquiv, Equiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_comp (Z := Z),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_comp rfl (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V'), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_pre_right (Z := Z)]

/-- 概要：入口の転置と輸送は始域側の前合成作用と合成を保つ。
方針：転置の合成保存と第二始域の自然性を適用する。
規約：元の右関手を保持する。
使われ方：前合成の Hom 対応の始域自然性。 -/
lemma precompositionSourceEquiv_precomp {A C D Z : SSet.{u}} [Quasicategory Z]
    (R : D ⟶ C) {U U' : A ⟶ (ihom C).obj Z} {V : A ⟶ (ihom D).obj Z}
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) :
    precompositionSourceEquiv (Z := Z) R U' V
      ((hoFunctor.map ((ihom A).map ((pre R).app Z))).toFunctor.map
        (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U'))
        (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)) γ ≫ α) =
    (hoFunctor.map ((pre R).app ((ihom A).obj Z))).toFunctor.map
      (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U')))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := Z) U' U γ) ≫
      precompositionSourceEquiv (Z := Z) R U V α := by
  let b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U' ≫ (pre R).app Z) (U ≫ (pre R).app Z) :=
    (hoFunctor.map ((ihom A).map ((pre R).app Z))).toFunctor.map
      (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U'))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)) γ
  change precompositionSourceEquiv (Z := Z) R U' V (b ≫ α) = _
  dsimp only [precompositionSourceEquiv, Equiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_comp (A := A) (B := D) (Z := Z)
      (U := U' ≫ (pre R).app Z) (V := U ≫ (pre R).app Z) (W := V),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceHomTransportEquiv_factor (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U')
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) R U), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_pre_right (Z := Z)]

/-- 概要：出口の転置と輸送は始域側の合成を保つ。
方針：転置と端点輸送の合成保存を順に適用する。
規約：元の Hom と左関手を保持する。
使われ方：前合成の Hom 対応の始域自然性。 -/
lemma precompositionTargetEquiv_precomp {A C D Z : SSet.{u}} [Quasicategory Z]
    (L : C ⟶ D) {U U' : A ⟶ (ihom C).obj Z} {V : A ⟶ (ihom D).obj Z}
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z)) :
    precompositionTargetEquiv (Z := Z) L U' V (γ ≫ α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := Z) U' U γ ≫ precompositionTargetEquiv (Z := Z) L U V α := by
  dsimp only [precompositionTargetEquiv, Equiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv_comp (Z := Z),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_comp rfl rfl (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V)]
  exact congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right (D := Z) L V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := Z) U (V ≫ (pre L).app Z) α))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomCongr_refl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (Z := Z) U' U γ))

/-- 概要：前合成の Hom 対応を二つの転置と明示した端点輸送で与える。
方針：元の Hom₁ 逆対応を表示した全単射を合成する。
規約：パラメータ A は任意。
使われ方：自然性の計算で輸送を可視にする。 -/
def precompositionTransposeEquiv {A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (V ≫ (pre L).app Z) :=
  (precompositionSourceEquiv (Z := Z) R U V).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V)).trans
      (precompositionTargetEquiv (Z := Z) L U V).symm)

/-- 概要：前合成の Hom 対応は転置後に元の Hom₁ 対応となる。
方針：転置と端点輸送の全単射の両逆を相殺する。
規約：元の指定 Hom に対する等式。
使われ方：前合成の自然性の証明。 -/
lemma precompositionTransposeEquiv_formula {A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (U : A ⟶ (ihom C).obj Z) (V : A ⟶ (ihom D).obj Z)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) :
    precompositionTargetEquiv (Z := Z) L U V (precompositionTransposeEquiv (Z := Z) a U V α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V)
        (precompositionSourceEquiv (Z := Z) R U V α) := by
  exact equivalenceTransfer_formula (precompositionSourceEquiv (Z := Z) R U V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv a (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose V))
    (precompositionTargetEquiv (Z := Z) L U V) α

/-- 概要：前合成の Hom 対応は標的の Hom の合成に自然。
方針：転置で単射性を判定し、元の随伴の自然性と端点輸送を計算する。
規約：パラメータと全関手圏の任意の射を保持する。
使われ方：前合成の全 QCat 随伴の Hom 対応。 -/
lemma precompositionTransposeEquiv_comp {A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    {U : A ⟶ (ihom C).obj Z} {V V' : A ⟶ (ihom D).obj Z}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V V') :
    precompositionTransposeEquiv (Z := Z) a U V' (α ≫ β) =
      precompositionTransposeEquiv (Z := Z) a U V α ≫
        (hoFunctor.map ((ihom A).map ((pre L).app Z))).toFunctor.map
          (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V))
          (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V')) β := by
  apply (precompositionTargetEquiv (Z := Z) L U V').injective
  rw [precompositionTransposeEquiv_formula (Z := Z), precompositionTargetEquiv_comp (Z := Z),
    precompositionTransposeEquiv_formula (Z := Z), precompositionSourceEquiv_comp (Z := Z),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_comp]

/-- 概要：前合成の Hom 対応は始域の Hom の合成に自然。
方針：転置後に右随伴による前合成の自然性を適用する。
規約：パラメータと元の二胞体を保持する。
使われ方：前合成の全 QCat 随伴の Hom 対応。 -/
lemma precompositionTransposeEquiv_precomp {A C D Z : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory Z]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    {U U' : A ⟶ (ihom C).obj Z} {V : A ⟶ (ihom D).obj Z}
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (pre R).app Z) V) :
    precompositionTransposeEquiv (Z := Z) a U' V
      ((hoFunctor.map ((ihom A).map ((pre R).app Z))).toFunctor.map
        (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U'))
        (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)) γ ≫ α) =
      γ ≫ precompositionTransposeEquiv (Z := Z) a U V α := by
  apply (precompositionTargetEquiv (Z := Z) L U' V).injective
  rw [precompositionTransposeEquiv_formula (Z := Z), precompositionTargetEquiv_precomp (Z := Z),
    precompositionTransposeEquiv_formula (Z := Z), precompositionSourceEquiv_precomp (Z := Z),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneEquiv_precomp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
