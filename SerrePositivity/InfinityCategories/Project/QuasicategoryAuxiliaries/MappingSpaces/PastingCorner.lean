module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PrismRetraction

/-! # 終端角を除いた長方形の収縮

概要：長方形から右上の終端頂点を除いた部分図式は、右の span へ right anodyne に制限できる。
方針：横座標を時刻に応じて max(x,t) に変え、左列を中央列へ動かす。
規約：頂点は (x,y)、除く頂点は (2,1)、右の span は横座標が非零の部分。
使われ方：S4 の貼り合わせにおける coslice の制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：右上の終端頂点を除いた長方形の全部分図式。
方針：各単体の全頂点が (2,1) 以外である条件を課す。
規約：任意の次数の退化単体も含む。
使われ方：貼り合わせの余錐の基底となる五頂点の図式。 -/
def pastingCorner : ((Δ[2] : SSet.{u}) ⊗ Δ[1]).Subcomplex where
  obj n := {s | ∀ j : Fin (n.unop.len + 1), (stdSimplex.objEquiv s.1).toOrderHom j = 2 →
    (stdSimplex.objEquiv s.2).toOrderHom j ≠ 1}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：五頂点の図式の右の span 部分。
方針：横座標が零でない頂点だけを残す。
規約：頂点は (1,0)、(2,0)、(1,1)。
使われ方：右四角形の span と余錐の圏の比較。 -/
def pastingRightSpan : (pastingCorner : SSet.{u}).Subcomplex where
  obj n := {s | ∀ j : Fin (n.unop.len + 1), (stdSimplex.objEquiv s.val.1).toOrderHom j ≠ 0}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：時間に応じて横座標を中央列まで上げる単調写像。
方針：元の座標と時間の最大値を取る。
規約：時間は零または一。使われ方：部分長方形の収縮。 -/
def pastingRaiseOrderHom : Fin 2 × Fin 3 →o Fin 3 where
  toFun p := max p.2 p.1.castSucc
  monotone' {a b} h := max_le_max h.2 (by exact h.1)

/-- 概要：横座標の単体を時間の単体に沿って中央列まで上げる。
方針：各頂点列を最大値の単調写像で合成する。
規約：全次数で自然。使われ方：部分長方形の prism。 -/
def pastingRaiseSimplex {n : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{u}).obj n) (x : (Δ[2] : SSet.{u}).obj n) :
    (Δ[2] : SSet.{u}).obj n :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (pastingRaiseOrderHom.comp ((stdSimplex.objEquiv t).toOrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom)))

private lemma raise_eq_last (t : Fin 2) (x : Fin 3) (h : max x t.castSucc = 2) : x = 2 := by
  fin_cases t <;> fin_cases x <;> simp_all

private lemma raise_fixed (t : Fin 2) (x : Fin 3) (h : x ≠ 0) : max x t.castSucc = x := by
  fin_cases t <;> fin_cases x <;> simp_all

private lemma raise_one_ne_zero (x : Fin 3) : max x (1 : Fin 3) ≠ 0 := by
  fin_cases x <;> decide

/-- 概要：左列を中央列へ動かす五頂点図式の prism。
方針：横座標を max(x,t) に写し、縦座標は保存する。
規約：t=0 は恒等射、t=1 は右の span への収縮。
使われ方：右の span の包含の right anodyne 性。 -/
def pastingCornerPrism : (Δ[1] : SSet.{u}) ⊗ (pastingCorner : SSet.{u}) ⟶
    (pastingCorner : SSet.{u}) where
  app n := ↾fun s ↦ ⟨(pastingRaiseSimplex s.1 s.2.val.1, s.2.val.2), by
    intro j h
    exact s.2.property j (raise_eq_last ((stdSimplex.objEquiv s.1).toOrderHom j)
      ((stdSimplex.objEquiv s.2.val.1).toOrderHom j) h)⟩
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · rfl

/-- 概要：prism の始点は五頂点図式の恒等射。
方針：max(x,0)=x を各頂点で計算する。
規約：射の厳密な等式。
使われ方：収縮の元の端点。 -/
lemma pastingCornerPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (pastingCorner : SSet.{u}) ≫ pastingCornerPrism = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact max_eq_left (Fin.zero_le (s.val.1 j))
  · rfl

/-- 概要：prism の終点を右の span の中の射として表示する。
方針：max(x,1) は零でないので像が右の span に含まれる。
規約：元の五頂点図式への包含との合成は prism の終点そのもの。
使われ方：right anodyne 性のための収縮射。 -/
def pastingCornerRetraction : (pastingCorner : SSet.{u}) ⟶ (pastingRightSpan : SSet.{u}) :=
  Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pastingCorner : SSet.{u}) ≫ pastingCornerPrism) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    intro j
    exact raise_one_ne_zero ((stdSimplex.objEquiv t.val.1).toOrderHom j))

/-- 概要：prism の終点は収縮射と包含の合成。
方針：部分複体への持ち上げの定義を使う。
規約：射の厳密な等式。
使われ方：収縮先での持ち上げの指定。 -/
lemma pastingCornerPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pastingCorner : SSet.{u}) ≫ pastingCornerPrism =
      pastingCornerRetraction ≫ pastingRightSpan.ι := rfl

/-- 概要：収縮射は右の span の上では恒等射。
方針：横座標が非零なら max(x,1)=x を使う。
規約：右の span の包含は厳密な切断。
使われ方：固定部分を持つ収縮の条件。 -/
lemma pastingRightSpan_retraction :
    pastingRightSpan.ι ≫ pastingCornerRetraction = 𝟙 (pastingRightSpan : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact raise_fixed 1 (s.val.val.1 j) (s.property j)
  · rfl

/-- 概要：prism は右の span を全時刻で固定する。
方針：横座標が一以上なら全ての区間座標より大きいことを使う。
規約：固定は単体的な射の等式。
使われ方：右 anodyne な収縮の相対条件。 -/
lemma pastingCornerPrism_fixed :
    (Δ[1] ◁ pastingRightSpan.ι) ≫ pastingCornerPrism =
      snd (Δ[1] : SSet.{u}) (pastingRightSpan : SSet.{u}) ≫ pastingRightSpan.ι := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  apply Subtype.ext
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact raise_fixed (t j) (s.val.val.1 j) (s.property j)
  · rfl

/-- 概要：右の span の五頂点図式への包含は right anodyne。
方針：恒等射から右の span への収縮を、その span を固定する prism として構成した結果を使う。
規約：値域の図式を選ぶ前の単体集合の性質。
使われ方：S4 の右四角形と部分長方形の coslice の比較。 -/
lemma pastingRightSpan_rightAnodyne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions pastingRightSpan.{u}.ι :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stable_rightAnodyneExtensions_of_prism_retraction pastingRightSpan pastingCornerRetraction
    pastingRightSpan_retraction pastingCornerPrism pastingCornerPrism_zero
    pastingCornerPrism_one pastingCornerPrism_fixed

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
