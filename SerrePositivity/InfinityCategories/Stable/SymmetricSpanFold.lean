module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeLoopProduct
public import SerrePositivity.InfinityCategories.Stable.CosliceDiagramChange

/-! # 対称 span の同じ二枝を一本の辺へ畳む

概要：同じ辺を二度使う span を一本の辺へ畳み、その余錐を全 span の余錐へ制限する。
方針：ホーンの二枝の pushout と join の前合成を使う。
規約：値域の充填性や零対象性は不要。使われ方：対角のループ単位を辺の余錐の像として表す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二枝の span を両枝で恒等となる一本の標準辺へ畳む。
方針：ホーンの二枝の pushout に二つの恒等射を入れる。
規約：両枝の向きを保つ。使われ方：同じ二枝の対角の余錐。 -/
def spanFold : (horn 2 0 : SSet.{u}) ⟶ Δ[1] :=
  horn₂₀.isPushout.desc (𝟙 _) (𝟙 _) rfl

/-- 概要：畳み込みの第一枝への制限は恒等。
方針：pushout の第一成分を計算する。
規約：0→1 の枝。使われ方：第一枝で同じ余錐を得る。 -/
lemma spanFold_left : horn₂₀.ι₀₁ ≫ spanFold.{u} = 𝟙 Δ[1] :=
  horn₂₀.isPushout.inl_desc _ _ _

/-- 概要：畳み込みの第二枝への制限は恒等。
方針：pushout の第二成分を計算する。
規約：0→2 の枝。使われ方：第二枝で同じ余錐を得る。 -/
lemma spanFold_right : horn₂₀.ι₀₂ ≫ spanFold.{u} = 𝟙 Δ[1] :=
  horn₂₀.isPushout.inr_desc _ _ _

/-- 概要：一本の辺を畳み込みで引き戻すと同じ辺を二度使う span になる。
方針：ホーンの二枝で比較する。
規約：図式の厳密な等号。使われ方：余錐の固定図式の条件を保つ。 -/
lemma spanFold_edgeSpan {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    spanFold ≫ (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge = edgeSpan f f := by
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc, spanFold_left, Category.id_comp, edgeSpan_left]
    rfl
  · rw [← Category.assoc, spanFold_right, Category.id_comp, edgeSpan_right]
    rfl

/-- 概要：一本の辺の余錐を同じ二枝の span の余錐へ畳み込みで送る。
方針：余錐の左因子に畳み込みを前合成する。
規約：終点は可変のまま保つ。使われ方：零頂点を経由する余錐の因子分解。 -/
def symmetricSpanFoldCoslice {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    sliceUnder ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge) ⟶
      sliceUnder (edgeSpan f f) where
  app n := ↾fun s => ⟨joinMap spanFold (𝟙 (stdSimplex.obj n.unop)) ≫ s.val, by
    calc
      _ = spanFold ≫ (joinInl (Δ[1] : SSet.{u}) _ ≫ s.val) := by
        rw [← Category.assoc, joinInl_joinMap, Category.assoc]
      _ = spanFold ≫ (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge :=
        congrArg (fun v => spanFold ≫ v) s.property
      _ = _ := spanFold_edgeSpan f⟩
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change joinMap spanFold (𝟙 _) ≫ (joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ s.val) =
      joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ (joinMap spanFold (𝟙 _) ≫ s.val)
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：畳み込みの coslice 射は、通常の図式制限を元の対称 span の表示へ揃えた射である。
方針：各単体で等号輸送が元の余錐を変えないことを使う。
規約：射そのものの等号。使われ方：展開した余錐族の計算。 -/
lemma symmetricSpanFoldCoslice_eq_restrict {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    symmetricSpanFoldCoslice f =
      sliceUnderRestrict ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge) spanFold ≫
        eqToHom (congrArg sliceUnder (spanFold_edgeSpan f)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  exact (stableCosliceDiagramChange_val (spanFold_edgeSpan f) n
    ((sliceUnderRestrict _ spanFold).app n s)).symm

/-- 概要：畳み込みによる余錐の射は終点射影を保つ。
方針：join の右包含の自然性を使う。
規約：射の厳密な等号。使われ方：終点固定余錐空間への制限。 -/
lemma symmetricSpanFoldCoslice_projection {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    symmetricSpanFoldCoslice f ≫ sliceUnderProjection (edgeSpan f f) =
      sliceUnderProjection ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInr _ _ ≫ (joinMap spanFold (𝟙 _) ≫ s.val)) =
    SSet.yonedaEquiv (joinInr _ _ ≫ s.val)
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]

/-- 概要：一本の辺の終点固定余錐を対称 span の終点固定余錐へ送る。
方針：畳み込みの coslice 射を終点の fiber へ制限する。
規約：元の図式の表示を変更しない。使われ方：ループ単位の代表元。 -/
def symmetricCoconeFold {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    coconeMappingSpace ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge) y ⟶
      coconeMappingSpace (edgeSpan f f) y :=
  vertexFiberMap _ _ (symmetricSpanFoldCoslice f) (symmetricSpanFoldCoslice_projection f) y

/-- 概要：畳み込みを終点固定余錐の族で展開すると join の左因子の畳み込みとなる。
方針：fiber の包含後の coslice の射を定義通り計算する。
規約：パラメーターは任意。使われ方：畳んだ余錐の両枝を計算する。 -/
lemma symmetricCoconeFold_uncurry {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (a : T ⟶ coconeMappingSpace ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge) y) :
    sliceUnderUncurry ((a ≫ symmetricCoconeFold f y) ≫
      vertexFiberι (sliceUnderProjection (edgeSpan f f)) y) =
      joinMap spanFold (𝟙 T) ≫
        sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection
          ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm f.edge)) y) := by
  change sliceUnderUncurry ((a ≫ vertexFiberι _ y) ≫ symmetricSpanFoldCoslice f) = _
  rw [symmetricSpanFoldCoslice_eq_restrict, ← Category.assoc,
    stableCosliceDiagramChange_uncurry (spanFold_edgeSpan f), sliceUnderUncurry_restrict]

end SerrePositivity.InfinityCategories
