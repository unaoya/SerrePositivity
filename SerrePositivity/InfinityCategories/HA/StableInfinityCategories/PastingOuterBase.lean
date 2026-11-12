module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingCorner
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRestriction

/-! # 外側 span への四頂点図式の収縮

概要：下側三角形と左辺からなる四頂点図式は外側 span へ right anodyne に制限できる。
方針：下辺の中点を終点へ動かし、それ以外の三頂点を固定する prism を作る。
規約：四頂点は (0,0)、(1,0)、(2,0)、(0,1)。
使われ方：S4 の左四角形の押し出し性を使う外側比較の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：下側三角形と左辺からなる四頂点の部分図式。
方針：縦座標一の頂点では横座標零を要求する。
規約：左四角形の右上角を含まない。使われ方：外側 span への収縮の始域。 -/
def pastingOuterBase : ((Δ[2] : SSet.{u}) ⊗ Δ[1]).Subcomplex where
  obj n := {s | ∀ j : Fin (n.unop.len + 1), (stdSimplex.objEquiv s.2).toOrderHom j = 1 →
    (stdSimplex.objEquiv s.1).toOrderHom j = 0}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：四頂点図式の外側 span 部分。
方針：下辺の中点を除く。
規約：三頂点は (0,0)、(2,0)、(0,1)。使われ方：外側四角形の基底。 -/
def pastingOuterSpan : (pastingOuterBase : SSet.{u}).Subcomplex where
  obj n := {s | ∀ j : Fin (n.unop.len + 1), (stdSimplex.objEquiv s.val.1).toOrderHom j ≠ 1}
  map α _ hs j := hs (α.unop.toOrderHom j)

/-- 概要：時間に応じて下辺の中点を右端へ上げる単調写像。
方針：有限順序集合の全ての比較を検査する。
規約：時間は零または一。使われ方：部分長方形の収縮。 -/
def pastingOuterRaiseOrderHom : Fin 2 × Fin 3 →o Fin 3 where
  toFun p := if p.2 = 0 then 0 else if p.1 = 0 then p.2 else 2
  monotone' := by decide

/-- 概要：横座標の単体を時間の単体に沿って右端へ動かす。
方針：各頂点列を有限の単調写像で合成する。
規約：全次数で自然。使われ方：部分長方形の prism。 -/
def pastingOuterRaiseSimplex {n : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{u}).obj n) (x : (Δ[2] : SSet.{u}).obj n) :
    (Δ[2] : SSet.{u}).obj n :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (pastingOuterRaiseOrderHom.comp ((stdSimplex.objEquiv t).toOrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom)))

private lemma raise_zero (t : Fin 2) : pastingOuterRaiseOrderHom (t, 0) = 0 := by
  exact (by decide : ∀ t : Fin 2, pastingOuterRaiseOrderHom (t, 0) = 0) t

private lemma raise_fixed (t : Fin 2) (x : Fin 3) (h : x ≠ 1) :
    pastingOuterRaiseOrderHom (t, x) = x := by
  exact (by decide : ∀ t : Fin 2, ∀ x : Fin 3,
    x ≠ 1 → pastingOuterRaiseOrderHom (t, x) = x) t x h

private lemma raise_one_ne_one (x : Fin 3) : pastingOuterRaiseOrderHom (1, x) ≠ 1 := by
  exact (by decide : ∀ x : Fin 3, pastingOuterRaiseOrderHom (1, x) ≠ 1) x

private lemma raise_time_zero (x : Fin 3) : pastingOuterRaiseOrderHom (0, x) = x := by
  exact (by decide : ∀ x : Fin 3, pastingOuterRaiseOrderHom (0, x) = x) x

/-- 概要：下辺の中点を右端へ動かす四頂点図式の prism。
方針：横座標零を固定し、非零の横座標を時刻一で二へ写す。
規約：t=0 は恒等射、t=1 は外側 span への収縮。
使われ方：外側 span の包含の right anodyne 性。 -/
def pastingOuterBasePrism : (Δ[1] : SSet.{u}) ⊗ (pastingOuterBase : SSet.{u}) ⟶
    (pastingOuterBase : SSet.{u}) where
  app n := ↾fun s ↦ ⟨(pastingOuterRaiseSimplex s.1 s.2.val.1, s.2.val.2), by
    intro j h
    change pastingOuterRaiseOrderHom (_, _) = 0
    rw [s.2.property j h]
    exact raise_zero _⟩
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

/-- 概要：prism の始点は四頂点図式の恒等射。
方針：時刻零の単調写像は恒等写像であることを使う。
規約：射の厳密な等式。
使われ方：収縮の元の端点。 -/
lemma pastingOuterBasePrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (pastingOuterBase : SSet.{u}) ≫ pastingOuterBasePrism = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    exact raise_time_zero (s.val.1 j)
  · rfl

/-- 概要：prism の終点を外側 span の中の射として表示する。
方針：時刻一の横座標は一でないので外側 span に入る。
規約：元の四頂点図式への包含との合成は prism の終点そのもの。
使われ方：right anodyne 性のための収縮射。 -/
def pastingOuterBaseRetraction : (pastingOuterBase : SSet.{u}) ⟶ (pastingOuterSpan : SSet.{u}) :=
  Subcomplex.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pastingOuterBase : SSet.{u}) ≫ pastingOuterBasePrism) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    intro j
    exact raise_one_ne_one ((stdSimplex.objEquiv t.val.1).toOrderHom j))

/-- 概要：prism の終点は収縮射と包含の合成。
方針：部分複体への持ち上げの定義を使う。
規約：射の厳密な等式。
使われ方：収縮先での持ち上げの指定。 -/
lemma pastingOuterBasePrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pastingOuterBase : SSet.{u}) ≫ pastingOuterBasePrism =
      pastingOuterBaseRetraction ≫ pastingOuterSpan.ι := rfl

/-- 概要：収縮射は外側 span の上では恒等射。
方針：横座標が零または二なら写像が固定することを使う。
規約：外側 span の包含は厳密な切断。
使われ方：固定部分を持つ収縮の条件。 -/
lemma pastingOuterSpan_retraction :
    pastingOuterSpan.ι ≫ pastingOuterBaseRetraction = 𝟙 (pastingOuterSpan : SSet.{u}) := by
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

/-- 概要：prism は外側 span を全時刻で固定する。
方針：横座標が一以外なら全時刻で固定されることを使う。
規約：固定は単体的な射の等式。
使われ方：右 anodyne な収縮の相対条件。 -/
lemma pastingOuterBasePrism_fixed :
    (Δ[1] ◁ pastingOuterSpan.ι) ≫ pastingOuterBasePrism =
      snd (Δ[1] : SSet.{u}) (pastingOuterSpan : SSet.{u}) ≫ pastingOuterSpan.ι := by
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

/-- 概要：外側 span の四頂点図式への包含は right anodyne。
方針：恒等射から外側 span への収縮を、その span を固定する prism として構成した結果を使う。
規約：値域の図式を選ぶ前の単体集合の性質。
使われ方：S4 の外側 span と四頂点図式の coslice の比較。 -/
lemma pastingOuterSpan_rightAnodyne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions pastingOuterSpan.{u}.ι :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stable_rightAnodyneExtensions_of_prism_retraction pastingOuterSpan pastingOuterBaseRetraction
    pastingOuterSpan_retraction pastingOuterBasePrism pastingOuterBasePrism_zero
    pastingOuterBasePrism_one pastingOuterBasePrism_fixed

/-- 概要：四頂点図式は終端角を除く五頂点図式に含まれる。
方針：縦座標一なら横座標零なので、終端角にはならない。
規約：同じ長方形の部分複体の包含。
使われ方：左四角形の余極限頂点を付け加える比較。 -/
lemma pastingOuterBase_le_corner : pastingOuterBase.{u} ≤ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner := by
  intro n s hs j hx hy
  have hz := hs j hy
  rw [hx] at hz
  exact (by decide : (2 : Fin 3) ≠ 0) hz

/-- 概要：四頂点図式から五頂点図式への包含。
方針：部分複体の包含関係から射を作る。
規約：両方の包含先は同じ長方形。
使われ方：外側比較の図式の制限。 -/
def pastingOuterBaseToCorner : (pastingOuterBase : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) :=
  Subcomplex.homOfLE pastingOuterBase_le_corner

/-- 概要：外側 span への四頂点図式の coslice の制限は trivial Kan fibration。
方針：固定部分つき収縮から得た right anodyne 性を使う。
規約：値域に quasicategory 性のみを仮定する。
使われ方：外側四角形の余極限判定。 -/
lemma pastingOuterBaseRestrict_trivialKanFibration {X : SSet.{u}} [Quasicategory X]
    (p : (pastingOuterBase : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p pastingOuterSpan.ι) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration p pastingOuterSpan.ι pastingOuterSpan_rightAnodyne

/-- 概要：四頂点図式上の余極限性は外側 span への制限で判定できる。
方針：right anodyne な包含による余極限性の保存と反映を適用する。
規約：余錐の頂点を変えない。値域は quasicategory。
使われ方：左四角形の押し出し性を使う外側比較の後半。 -/
lemma pastingOuterBase_isColimitCone_iff_outerSpan {X : SSet.{u}} [Quasicategory X]
    {p : (pastingOuterBase : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict pastingOuterSpan.ι) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_rightAnodyne c pastingOuterSpan.ι pastingOuterSpan_rightAnodyne

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
