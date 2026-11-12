module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftResolutionComparison

/-!
概要：左解像への標準比較を越える strict な図式の比較の延長。
方針：標準比較の単射性と対象ごとの同値性を使い、strict transport への延長空間を可縮にする。
規約：逆向きの比較は全対象で同時に自然な変換として取り、対象ごとには選ばない。
使われ方：Kerodon §§4.6.7（Tag 01LA）、5.6.5（Tag 028U）、左 fiber の旗の解像と strict transport の高次の比較の接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：左解像への標準比較は単射。
方針：二重反転の同型と、右解像への単射の反転を合成する。
規約：Kan 性を要求しない。
使われ方：Kerodon §4.6.7（Tag 01LA）、標準比較を固定した strict な延長の包含。 -/
instance coherentLeftResolutionComparison_mono (X : SSet.{u}) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y h
  have hv := congrArg SSet.opObjEquiv h
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison X.op).app (SimplexCategory.rev.op.obj n)
      (SSet.opObjEquiv.symm x) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison X.op).app (SimplexCategory.rev.op.obj n)
      (SSet.opObjEquiv.symm y) at hv
  have hxy := (mono_iff_injective
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison X.op).app (SimplexCategory.rev.op.obj n))).mp inferInstance hv
  exact SSet.opObjEquiv.symm.injective hxy

/-- 概要：通常の左解像関手の値も Kan 複体。
方針：既存の左解像の Kan 性へ定義で戻す。
規約：図式の合成として値を表示した場合の充填性の推論を可能にする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、延長した自然変換の成分の同値性の判定。 -/
instance coherentLeftResolutionFunctor_obj_kanComplex (X : SSet.{u}) [KanComplex X] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor.obj X) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution X))

/-- 概要：図式の値ごとの左解像の標準比較を通常の自然変換にまとめる。
方針：左解像の標準比較の自然性を各成分の射に適用する。
規約：成分は既存の coherentLeftResolutionComparison そのもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、図式全体の比較を保った解像への延長。 -/
noncomputable def leftResolutionDiagramComparison {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) : F ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor where
  app c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison (F.obj c)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparisonNat.naturality (F.map f)

/-- 概要：左解像を越えて strict transport への比較を延長する空間は可縮な Kan 複体。
方針：成分ごとの標準比較の単射性と同値性を、図式の延長空間の判定へ適用する。
規約：元の比較 θ を厳密に固定する。
使われ方：Kerodon §§5.6.5（Tag 028U）–5.6.8（Tag 02S9）、左解像を用いる比較の存在と高次の一意性。 -/
lemma leftResolutionDiagramExtensionSpace_isContractibleKan
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramExtensionSpace (leftResolutionDiagramComparison F) q θ) := by
  have : ∀ c, KanComplex ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor).obj c) :=
    fun c ↦ inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution (F.obj c)))
  have : ∀ c, Mono ((leftResolutionDiagramComparison F).app c) :=
    fun c ↦ coherentLeftResolutionComparison_mono (F.obj c)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramExtensionSpace_isContractibleKan (leftResolutionDiagramComparison F)
    (fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison_isQCatEquivalence (F.obj c)) q θ

/-- 概要：strict transport の図式への左解像の比較は図式全体として厳密な左逆を持つ。
方針：strict transport の恒等比較を左解像の図式へ延長する。
規約：左逆は自然変換であり、往復は自然変換の等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な旗の解像から strict な比較へ戻す。 -/
lemma exists_leftStrictTransportResolutionRetraction
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q,
      leftResolutionDiagramComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≫ r =
        𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) := by
  have : ∀ c, KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor).obj c) :=
    fun c ↦ inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c)))
  have : ∀ c, Mono ((leftResolutionDiagramComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)).app c) :=
    fun c ↦ coherentLeftResolutionComparison_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_strictDiagramExtension
    (leftResolutionDiagramComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q))
    (fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c)) q (𝟙 _)

/-- 概要：同値な比較の左解像への厳密な延長も対象ごとに同値。
方針：元の比較と左解像の標準比較の同値性に二対三則を適用する。
規約：任意に指定された厳密な延長 r について述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、延長した図式全体の比較を関手同型へ移す。 -/
lemma leftResolutionDiagramExtension_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{u}} (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (θ : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) (hθ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (θ.app c))
    (r : F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q)
    (hr : leftResolutionDiagramComparison F ≫ r = θ) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution (F.obj c))
      (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c) (r.app c) := by
  have h := congrArg (fun t : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q ↦ t.app c) hr
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison (F.obj c) ≫ r.app c = θ.app c at h
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionComparison_isQCatEquivalence (F.obj c)).cancel_left
  rw [h]
  exact hθ c

/-- 概要：strict transport の左解像には、図式全体の厳密な左逆で対象ごとに同値なものが存在する。
方針：恒等比較の厳密な延長を取り、延長の対象ごとの同値性を使う。
規約：左逆と同値性を同じ自然変換 r について同時に与える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、旗の解像を介した coherent な比較を strict な比較へ戻す。 -/
lemma exists_leftStrictTransportResolutionRetraction_equivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (q : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolutionFunctor ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q,
      leftResolutionDiagramComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ≫ r =
        𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) ∧ ∀ c,
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentLeftResolution (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c))
            (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c) (r.app c) := by
  obtain ⟨r, hr⟩ := exists_leftStrictTransportResolutionRetraction q
  refine ⟨r, hr, ?_⟩
  intro c
  exact leftResolutionDiagramExtension_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) q
    (𝟙 _) (fun c ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c))).isQCatEquivalence)
    r hr c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
