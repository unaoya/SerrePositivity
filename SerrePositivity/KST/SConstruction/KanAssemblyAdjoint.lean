module
public import SerrePositivity.KST.SConstruction.PointedExtensionSpace
public import SerrePositivity.KST.SConstruction.SuspensionAssemblyAdjoint
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison

/-! # 反復 S の随伴射の Kan な源への延長
概要：標的を Kan 置換した随伴射は源の Kan 置換に延長でき、その選択空間は可縮 Kan。
方針：loop の標的の Kan 性と置換の anodyne 単位を延長空間の一般定理へ渡す。
規約：選んだ延長の厳密な自然性・Ω 条件はここでは主張しない。使われ方：段の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：反復の Kan 境界商の loop の関手。
方針：円からの点つき内部 Hom を後合成する。
規約：L9 の Ω をそのまま使う。使われ方：Kan な随伴射の標的。 -/
def loopBoundaryKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  boundaryKanRealizationFunctor r ⋙
    PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}

/-- 概要：Kan 境界商の loop の各値は Kan。
方針：Kan 標的から作る L9 の loop の Kan 性。
規約：追加仮定なし。使われ方：anodyne 単位に沿う延長。 -/
instance loopBoundaryKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((loopBoundaryKanFunctor r).obj X).right) := Spectra.loopSpace_kanComplex _

/-- 概要：標的を Kan 置換した随伴射の自然変換。
方針：元の随伴射と、標的の置換の単位を loop で写した射を合成する。
規約：源はまだ未置換の境界商。使われ方：源の Kan 置換への延長の入力。 -/
def kanTargetAssemblyAdjointNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ loopBoundaryKanFunctor (r + 1) :=
  oneDirectionAssemblyAdjointNat r ≫ Functor.whiskerRight
    (Functor.whiskerLeft (boundaryReducedRealizationFunctor (r + 1)) Spectra.PointedKanReplacement.unit)
    (PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u})

/-- 概要：随伴射を源の Kan 置換へ延長する選択空間。
方針：置換の単位による写像空間の制限の fiber を取る。
規約：元の随伴射への制限を厳密に固定する。使われ方：Kan な段の接続の選択。 -/
def kanAssemblyAdjointChoices (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  pointedExtensionSpace (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((kanTargetAssemblyAdjointNat r).app X)

/-- 概要：随伴射の Kan な源への延長の選択空間は可縮 Kan。
方針：置換の単位の anodyne 性と loop の Kan 性を使う。
規約：延長の存在や Ω 条件を追加仮定しない。使われ方：高次の選択の制御。 -/
lemma kanAssemblyAdjointChoices_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kanAssemblyAdjointChoices r X) :=
  pointedExtensionSpace_isContractibleKan _ (Spectra.PointedKanReplacement.unit_anodyne _)
    ((kanTargetAssemblyAdjointNat r).app X)

/-- 概要：選択空間の頂点から Kan 複体間の実際の随伴射を取り出す。
方針：延長空間の写像の取り出しを使う。
規約：頂点を明示し、厳密な自然な選択はしない。使われ方：Ω 条件の検証対象。 -/
def kanAssemblyAdjointAt (r : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    (oneDirectionKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X :=
  pointedExtensionMap _ ((kanTargetAssemblyAdjointNat r).app X) v

/-- 概要：Kan な源への随伴射の延長は元の随伴射へ厳密に制限される。
方針：延長空間の fiber の関係式。
規約：全ての選択空間の頂点に適用。使われ方：元の suspension の射との整合性。 -/
lemma kanAssemblyAdjointAt_fac (r : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X) ≫
        kanAssemblyAdjointAt r X v = (kanTargetAssemblyAdjointNat r).app X :=
  pointedExtensionMap_fac _ _ v

/-- 概要：源と標的を Kan 模型にした随伴射の延長は実際に存在する。
方針：可縮な選択空間の非空性を使う。
規約：ここでは同値性を結論に含めない。使われ方：Kan な段の比較への接続。 -/
lemma exists_kanAssemblyAdjoint (r : ℕ) (X : StableModel.{u}) :
    ∃ k : (oneDirectionKanRealizationFunctor r).obj X ⟶ (loopBoundaryKanFunctor (r + 1)).obj X,
      Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X) ≫ k =
        (kanTargetAssemblyAdjointNat r).app X :=
  exists_pointedExtension _ (Spectra.PointedKanReplacement.unit_anodyne _)
    ((kanTargetAssemblyAdjointNat r).app X)

/-- 概要：随伴射の Kan 延長の選択空間は Kan 複体。
方針：可縮 Kan 性から充填を得る。
規約：追加仮定なし。使われ方：選択空間の高次の比較。 -/
instance kanAssemblyAdjointChoices_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (kanAssemblyAdjointChoices r X) :=
  (kanAssemblyAdjointChoices_isContractibleKan r X).kanComplex

/-- 概要：Kan 延長のパラメータ族を任意の単射に沿って相対的に補完できる。
方針：延長空間の一般の相対持ち上げを使う。
規約：元の随伴射への制限と既存の選択を厳密に保つ。使われ方：段の接続の整合性。 -/
lemma kanAssemblyAdjointChoices_relative_lifting (r : ℕ) (X : StableModel.{u})
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ kanAssemblyAdjointChoices r X) :
    ∃ b : T ⟶ kanAssemblyAdjointChoices r X, j ≫ b = a :=
  pointedExtensionSpace_relative_lifting _ (Spectra.PointedKanReplacement.unit_anodyne _)
    ((kanTargetAssemblyAdjointNat r).app X) j a

end SerrePositivity.KST.SConstruction
