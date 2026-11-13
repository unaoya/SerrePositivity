module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # cospan・span の極限から fiber/cofiber を構成する

概要：零対象があるとき、cospan の極限と span の余極限から各射の fiber/cofiber を構成する。
方針：二辺をホーンに貼り、join の錐を正方形へ移す。
規約：辺と零角を実際の単体的射として固定する。使われ方：HA 1.1.3.4 の十分条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 概要：辺の始点への制限は始点の定値射。
方針：Yoneda で辺の始点条件に帰着する。
規約：δ₁ が始点。使われ方：span の貼り合わせ。 -/
lemma edgeSimplex_source {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge = SSet.yonedaEquiv.symm x := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact f.src_eq

/-- 概要：辺の終点への制限は終点の定値射。
方針：Yoneda で辺の終点条件に帰着する。
規約：δ₀ が終点。使われ方：cospan の貼り合わせ。 -/
lemma edgeSimplex_target {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge = SSet.yonedaEquiv.symm y := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact f.tgt_eq

/-- 概要：終点を共有する二辺を cospan ホーンへ貼る。
方針：Λ[2,2] の辺の pushout の普遍性を使う。
規約：第一辺は 0→2、第二辺は 1→2。使われ方：fiber の極限図式。 -/
def edgeCospan {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z) :
    (horn 2 2 : SSet.{u}) ⟶ X :=
  horn₂₂.isPushout.desc (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)
    ((edgeSimplex_target f).trans (edgeSimplex_target g).symm)

/-- 概要：cospan の第一辺への制限は元の辺。
方針：pushout の第一包含の式を使う。
規約：0→2。使われ方：fiber の入力の固定。 -/
lemma edgeCospan_left {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z) :
    horn₂₂.ι₀₂ ≫ edgeCospan f g = SSet.yonedaEquiv.symm f.edge :=
  horn₂₂.isPushout.inl_desc _ _ _

/-- 概要：cospan の第二辺への制限は元の辺。
方針：pushout の第二包含の式を使う。
規約：1→2。使われ方：零対象からの辺の固定。 -/
lemma edgeCospan_right {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z) :
    horn₂₂.ι₁₂ ≫ edgeCospan f g = SSet.yonedaEquiv.symm g.edge :=
  horn₂₂.isPushout.inr_desc _ _ _

/-- 概要：始点を共有する二辺を span ホーンへ貼る。
方針：Λ[2,0] の辺の pushout の普遍性を使う。
規約：第一辺は 0→1、第二辺は 0→2。使われ方：cofiber の余極限図式。 -/
def edgeSpan {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    (horn 2 0 : SSet.{u}) ⟶ X :=
  horn₂₀.isPushout.desc (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)
    ((edgeSimplex_source f).trans (edgeSimplex_source g).symm)

/-- 概要：span の第一辺への制限は元の辺。
方針：pushout の第一包含の式を使う。
規約：0→1。使われ方：cofiber の入力の固定。 -/
lemma edgeSpan_left {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    horn₂₀.ι₀₁ ≫ edgeSpan f g = SSet.yonedaEquiv.symm f.edge :=
  horn₂₀.isPushout.inl_desc _ _ _

/-- 概要：span の第二辺への制限は元の辺。
方針：pushout の第二包含の式を使う。
規約：0→2。使われ方：零対象への辺の固定。 -/
lemma edgeSpan_right {X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) :
    horn₂₀.ι₀₂ ≫ edgeSpan f g = SSet.yonedaEquiv.symm g.edge :=
  horn₂₀.isPushout.inr_desc _ _ _

/-- 概要：cospan 上の錐を四角形へ直す。
方針：A2g の正方形同型の逆射で前合成する。
規約：図式を変えない。使われ方：有限極限からの引き戻し四角形。 -/
def coneSquare {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    Δ[1] ⊗ Δ[1] ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ c.val

/-- 概要：錐から作る四角形の cospan は元の図式。
方針：正方形同型の逆則と錐の固定条件を使う。
規約：図式の実際の等式。使われ方：極限性の移送。 -/
lemma coneSquare_cospan {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (coneSquare c) = p := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, coneSquare]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact c.property

private lemma limit_congr {K X : SSet.{u}} {p q : K ⟶ X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q}
    (hp : p = q) (hc : c.val = d.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  subst q
  have h : c = d := Subtype.ext hc
  rw [h]

/-- 概要：極限錐から作る四角形は引き戻し四角形。
方針：元の錐と四角形の引き戻し錐を図式の等式で比較する。
規約：h の極限に置き換えない。使われ方：finite-limit 判定からの fiber 構成。 -/
lemma coneSquare_isPullback {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (coneSquare c) :=
  (limit_congr (coneSquare_cospan c) (by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, coneSquare]
    rw [Iso.hom_inv_id_assoc])).2 hc

/-- 概要：span 上の余錐を四角形へ直す。
方針：余錐と正方形の同型の逆射で前合成する。
規約：図式を変えない。使われ方：有限余極限からの押し出し四角形。 -/
def coconeSquare {X : SSet.{u}} {p : (horn 2 0 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    Δ[1] ⊗ Δ[1] ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ c.val

/-- 概要：余錐から作る四角形の span は元の図式。
方針：正方形同型の逆則と固定条件を使う。
規約：図式の実際の等式。使われ方：余極限性の移送。 -/
lemma coconeSquare_span {X : SSet.{u}} {p : (horn 2 0 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (coconeSquare c) = p := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary, coconeSquare]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact c.property

private lemma colimit_congr {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q} (hp : p = q) (hc : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  subst q
  have h : c = d := Subtype.ext hc
  rw [h]

/-- 概要：余極限余錐から作る四角形は押し出し四角形。
方針：元の余錐と四角形の余錐の二つの射が同じことを使う。
規約：coslice の始対象の性質を保つ。使われ方：finite-colimit 判定からの cofiber 構成。 -/
lemma coconeSquare_isPushout {X : SSet.{u}} {p : (horn 2 0 : SSet.{u}) ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (coconeSquare c) :=
  (colimit_congr (coconeSquare_span c) (by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone, coconeSquare]
    rw [Iso.hom_inv_id_assoc])).2 hc

/-- 概要：極限錐の四角形の右辺は cospan の第一辺。
方針：cospan の包含の右辺計算を使う。
規約：元の図式を保持。使われ方：fiber の入力の固定。 -/
lemma coneSquare_right {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ coneSquare c = horn₂₂.ι₀₂ ≫ p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, Category.assoc]
  change horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (coneSquare c) = _
  rw [coneSquare_cospan]

/-- 概要：極限錐の四角形の上辺は cospan の第二辺。
方針：cospan の包含の上辺計算を使う。
規約：始点は零角。使われ方：fiber の零対象の固定。 -/
lemma coneSquare_top {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ coneSquare c = horn₂₂.ι₁₂ ≫ p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, Category.assoc]
  change horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (coneSquare c) = _
  rw [coneSquare_cospan]

/-- 概要：余極限余錐の四角形の下辺は span の第一辺。
方針：span の包含の辺の計算を使う。
規約：元の射を保持。使われ方：cofiber の入力の固定。 -/
lemma coconeSquare_bottom {X : SSet.{u}} {p : (horn 2 0 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ coconeSquare c = horn₂₀.ι₀₁ ≫ p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, Category.assoc]
  change horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (coconeSquare c) = _
  rw [coconeSquare_span]

/-- 概要：余極限余錐の四角形の左辺は span の第二辺。
方針：span の包含の辺の計算を使う。
規約：終点は零角。使われ方：cofiber の零対象の固定。 -/
lemma coconeSquare_left {X : SSet.{u}} {p : (horn 2 0 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ coconeSquare c = horn₂₀.ι₀₂ ≫ p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge, Category.assoc]
  change horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (coconeSquare c) = _
  rw [coconeSquare_span]

/-- 概要：四角形の上辺の始点は零角 (0,1) である。
方針：Yoneda の自然性で端点の値を計算する。
規約：δ₁ が辺の始点。使われ方：cospan の零対象の確認。 -/
lemma squareTopEdge_source {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ F)) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ => F.app _ s)
  apply Prod.ext <;> decide

/-- 概要：四角形の左辺の終点は零角 (0,1) である。
方針：Yoneda の自然性で端点の値を計算する。
規約：δ₀ が辺の終点。使われ方：span の零対象の確認。 -/
lemma squareLeftEdge_target {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    X.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F)) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1 := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
  apply congrArg (fun s : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ => F.app _ s)
  apply Prod.ext <;> decide

/-- 概要：零対象と cospan の極限から指定射の fiber 四角形を構成できる。
方針：零対象から終域への辺を貼り、極限錐を四角形へ戻す。
規約：元の射が右辺に一致する。使われ方：HA 1.1.3.4 の fiber の存在。 -/
lemma exists_fiberSquare_of_cospan_limits {X : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (hlim : ∀ p : (horn 2 2 : SSet.{u}) ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {x y : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X
  let g := Classical.choice (z.isInitial.nonempty_edge y)
  obtain ⟨c, hc⟩ := hlim (edgeCospan f g)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ coneSquare c = SSet.yonedaEquiv.symm f.edge := by
    rw [coneSquare_right, edgeCospan_left]
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ coneSquare c = SSet.yonedaEquiv.symm g.edge := by
    rw [coneSquare_top, edgeCospan_right]
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (coneSquare c) 0 1 = z.vertex := by
    rw [← squareTopEdge_source, hg]
    exact (congrArg (fun v : X _⦋1⦌ => X.δ 1 v)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply g.edge)).trans g.src_eq
  exact ⟨{ square := coneSquare c
           zero_corner := hz.symm ▸ z.isZero
           right_edge := he
           isPullback := coneSquare_isPullback c hc }⟩

/-- 概要：零対象と span の余極限から指定射の cofiber 四角形を構成できる。
方針：始域から零対象への辺を貼り、余極限余錐を四角形へ戻す。
規約：元の射が下辺に一致する。使われ方：HA 1.1.3.4 の cofiber の存在。 -/
lemma exists_cofiberSquare_of_span_colimits {X : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
    (hcolim : ∀ p : (horn 2 0 : SSet.{u}) ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    {x y : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X
  let g := Classical.choice (z.isTerminal.nonempty_edge x)
  obtain ⟨c, hc⟩ := hcolim (edgeSpan f g)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ coconeSquare c = SSet.yonedaEquiv.symm f.edge := by
    rw [coconeSquare_bottom, edgeSpan_left]
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ coconeSquare c = SSet.yonedaEquiv.symm g.edge := by
    rw [coconeSquare_left, edgeSpan_right]
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (coconeSquare c) 0 1 = z.vertex := by
    rw [← squareLeftEdge_target, hg]
    exact (congrArg (fun v : X _⦋1⦌ => X.δ 0 v)
      ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply g.edge)).trans g.tgt_eq
  exact ⟨{ square := coconeSquare c
           zero_corner := hz.symm ▸ z.isZero
           bottom_edge := he
           isPushout := coconeSquare_isPushout c hc }⟩

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
