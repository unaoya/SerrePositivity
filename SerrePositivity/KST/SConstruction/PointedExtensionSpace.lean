module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.KST.Spectra.PointedMappingFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-! # anodyne 射に沿う点つき延長の可縮な選択空間
概要：Kan 標的への点つき射の anodyne 延長の選択空間は可縮 Kan 複体。
方針：点つき内部 Hom の制限を指定した頂点へ引き戻し、全境界の持ち上げ性を使う。
規約：元の源の Kan 性は不要。使われ方：S の随伴射の Kan 置換への延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定した点つき射を延長する写像の空間。
方針：点つき写像空間の源の制限を指定した頂点で引き戻す。
規約：等号で固定した厳密な fiber。使われ方：延長の存在と高次の選択。 -/
def pointedExtensionSpace {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
    (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))

/-- 概要：延長の空間から一点への射影は trivial Kan fibration。
方針：anodyne な源の制限の全単射 RLP を基底変換する。
規約：標的のみ Kan を要求する。使われ方：選択空間の可縮性。 -/
lemma pointedExtensionSpace_projection_trivialKanFibration {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
      (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right :=
    ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp i hi Z⟩
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ hp.mem⟩

/-- 概要：点つき延長の選択空間は可縮 Kan。
方針：一点への射影に全境界を持ち上げる。
規約：源の Kan 性や追加の延長の存在は仮定しない。使われ方：coherent な Kan 延長。 -/
lemma pointedExtensionSpace_isContractibleKan {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (pointedExtensionSpace i h) := by
  have hp := pointedExtensionSpace_projection_trivialKanFibration i hi h
  intro n b
  have := hp.mem (boundary n).ι inferInstance
  have sq : CommSq b (boundary n).ι
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
        (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h)))
      (stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：延長の選択空間の頂点から実際の点つき射を取り出す。
方針：第一射影の頂点を写像空間の頂点の Hom 同値で戻す。
規約：取り出しに Kan 性は不要。使われ方：Kan 模型への実際の射。 -/
def pointedExtensionMap {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (v : (pointedExtensionSpace i h) _⦋0⦌) : B ⟶ Z :=
  Spectra.PointedMapping.familyMap B Z
    ((pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
      (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))).app (Opposite.op ⦋0⦌) v)

/-- 概要：選択空間から取り出した射は指定した射を厳密に延長する。
方針：fiber の可換式を頂点で評価し、写像空間の前合成の式を使う。
規約：点つき射の厳密等号。使われ方：元の随伴射との整合性。 -/
lemma pointedExtensionMap_fac {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (v : (pointedExtensionSpace i h) _⦋0⦌) : i ≫ pointedExtensionMap i h v = h := by
  apply (Spectra.PointedMapping.familyVertexEquiv A Z).injective
  change Spectra.PointedMapping.familyVertex (i ≫ pointedExtensionMap i h v) =
    Spectra.PointedMapping.familyVertex h
  rw [← Spectra.PointedMapping.familyVertex_pre]
  unfold pointedExtensionMap
  rw [Spectra.PointedMapping.familyVertex_familyMap]
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (pullback.condition (f := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right)
      (g := SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))) (Opposite.op ⦋0⦌)) v
  have hv : (pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
      (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))).app (Opposite.op ⦋0⦌) v =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right.app (Opposite.op ⦋0⦌)
      ((pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
        (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))).app (Opposite.op ⦋0⦌) v) =
    (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h)).app (Opposite.op ⦋0⦌)
      ((pullback.snd (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
        (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))).app (Opposite.op ⦋0⦌) v) at hc
  rw [hv, SSet.yonedaEquiv_symm_app_id] at hc
  exact hc

/-- 概要：Kan 標的への射は点つき anodyne 射に沿って延長できる。
方針：可縮な選択空間の頂点から実際の延長を取る。
規約：頂点での存在を追加仮定しない。使われ方：Kan 置換への随伴射の延長。 -/
lemma exists_pointedExtension {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right] :
    ∃ k : B ⟶ Z, i ≫ k = h := by
  obtain ⟨v⟩ := (pointedExtensionSpace_isContractibleKan i hi h).nonempty
  exact ⟨pointedExtensionMap i h v, pointedExtensionMap_fac i h v⟩

/-- 概要：延長の選択の任意のパラメータ族を単射に沿って相対的に延ばせる。
方針：可縮性を終対象への trivial Kan fibration として使う。
規約：既存部分での選択を厳密に保つ。使われ方：高次の延長の選択の整合性。 -/
lemma pointedExtensionSpace_relative_lifting {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right]
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ pointedExtensionSpace i h) :
    ∃ b : T ⟶ pointedExtensionSpace i h, j ≫ b = a := by
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).1
    (pointedExtensionSpace_isContractibleKan i hi h)
  have := hp.mem j inferInstance
  have sq : CommSq a j (terminal.from (pointedExtensionSpace i h)) (terminal.from T) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.KST.SConstruction
