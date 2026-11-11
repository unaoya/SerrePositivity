module
public import SerrePositivity.KST.SConstruction.KanAssemblyNaturality
public import SerrePositivity.KST.Spectra.PointedHomotopy

/-! # Kan な随伴射の誘導写像
概要：全自然数次数の誘導写像は延長の選択に依存せず、入力の射について自然。
方針：基点固定ホモトピーを L9 の相対ホモトピーへ移し、π の不変性を使う。
規約：零次数は集合として扱う。使われ方：段の接続の自然な π 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：随伴射の全自然数次数の誘導写像は選択によらない。
方針：二つの選択の基点固定ホモトピーに π のホモトピー不変性を適用する。
規約：基点は L9 の点つき対象の基点。使われ方：選択によらない誘導写像。 -/
lemma kanAssemblyAdjointAt_piMap_eq (r n : ℕ) (X : StableModel.{u})
    (v w : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X v) =
      Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X w) := by
  obtain ⟨H, hH⟩ := kanAssemblyAdjointAt_homotopy r X v w
  funext a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy n _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy _ _ H hH) a

/-- 概要：随伴射の全自然数次数の誘導写像は入力の射について自然。
方針：ホモトピー自然性に π の不変性を適用し、合成の法則で書き直す。
規約：両側の延長の選択は任意。使われ方：自然変換の成分の可換性。 -/
lemma kanAssemblyAdjointAt_piMap_naturality (r n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy ((oneDirectionKanRealizationFunctor r).obj X).right n
      ((oneDirectionKanRealizationFunctor r).obj X).basepoint) :
    Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r Y w)
        (Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map f) a) =
      Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor (r + 1)).map f)
        (Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X v) a) := by
  obtain ⟨H, hH⟩ := kanAssemblyAdjointAt_naturality_homotopy r f v w
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy n _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy _ _ H hH) a
  rw [← Spectra.pointedHomotopyMap_comp, ← Spectra.pointedHomotopyMap_comp]
  exact h

/-- 概要：一次方向の Kan な実現の基点での全次数ホモトピー集合の関手。
方針：L9 の誘導写像と恒等・合成の法則を束ねる。
規約：次数 n は固定。使われ方：随伴射の π による自然変換の源。 -/
def oneDirectionHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy ((oneDirectionKanRealizationFunctor r).obj X).right n
    ((oneDirectionKanRealizationFunctor r).obj X).basepoint
  map f := ↾(Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map f))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map (𝟙 X)) a = a
    rw [CategoryTheory.Functor.map_id, Spectra.pointedHomotopyMap_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map (f ≫ g)) a =
      Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map g)
        (Spectra.pointedHomotopyMap n ((oneDirectionKanRealizationFunctor r).map f) a)
    rw [CategoryTheory.Functor.map_comp, Spectra.pointedHomotopyMap_comp]

/-- 概要：次の Kan 境界商の loop の基点でのホモトピー集合の関手。
方針：L9 の誘導写像の関手法則を使う。
規約：r は loop を取る段の番号。使われ方：随伴射の π による自然変換の標的。 -/
def loopBoundaryHomotopyFunctor (r n : ℕ) : StableModel.{u} ⥤ Type u where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy ((loopBoundaryKanFunctor r).obj X).right n
    ((loopBoundaryKanFunctor r).obj X).basepoint
  map f := ↾(Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor r).map f))
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor r).map (𝟙 X)) a = a
    rw [CategoryTheory.Functor.map_id, Spectra.pointedHomotopyMap_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    change Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor r).map (f ≫ g)) a =
      Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor r).map g)
        (Spectra.pointedHomotopyMap n ((loopBoundaryKanFunctor r).map f) a)
    rw [CategoryTheory.Functor.map_comp, Spectra.pointedHomotopyMap_comp]

/-- 概要：Kan 延長の選択によらないホモトピー集合の自然変換。
方針：可縮な選択空間から頂点を選び、任意の選択間のホモトピー自然性を使う。
規約：全自然数次数を含む。使われ方：反復 S の段の接続の π 比較。 -/
def kanAssemblyHomotopyNat (r n : ℕ) :
    oneDirectionHomotopyFunctor r n ⟶ loopBoundaryHomotopyFunctor (r + 1) n where
  app X := ↾(Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X
    (kanAssemblyAdjointChoices_isContractibleKan r X).nonempty.some))
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact kanAssemblyAdjointAt_piMap_naturality r n f _ _ a

/-- 概要：自然変換の成分は任意の選択した延長から計算できる。
方針：誘導写像の選択独立性を適用する。
規約：自然変換の内部で使った選択を指定する必要はない。使われ方：成分の具体的な比較。 -/
lemma kanAssemblyHomotopyNat_app (r n : ℕ) (X : StableModel.{u})
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    (kanAssemblyHomotopyNat r n).app X =
      ↾(Spectra.pointedHomotopyMap n (kanAssemblyAdjointAt r X v)) := by
  apply ConcreteCategory.hom_ext
  intro a
  exact congrFun (kanAssemblyAdjointAt_piMap_eq r n X _ v) a

end SerrePositivity.KST.SConstruction
