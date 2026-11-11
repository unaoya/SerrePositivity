module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
概要：右 pinched 写像空間の連結成分とホモトピー圏の射の比較。
方針：零単体を辺と同定し、一次単体の三角形を右ホモトピーと比較する。
規約：N レーンの pinchedHom の定義をそのまま使う。
使われ方：HTT §1.2.2–1.2.3、Kerodon §4.6.5（Tag 01KW）。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：零次の定値単体は元の頂点。
方針：零次の唯一の射が恒等であることを使う。
規約：任意の単体集合の頂点を扱う。
使われ方：Kerodon §4.6.5（Tag 01KW） の写像空間の零単体。 -/
lemma pinchedConstant_zero {X : SSet.{u}} (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0 = x := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
  rw [show SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ from Subsingleton.elim _ _]
  exact CategoryTheory.Functor.map_id_apply X _ x

/-- 概要：一次の定値単体は退化した恒等辺。
方針：一次から零次への射の一意性を使う。
規約：恒等辺は二切断の Edge のもの。
使われ方：Kerodon §4.6.5（Tag 01KW） の写像空間の一次単体の三角形。 -/
lemma pinchedConstant_one {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 = (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge := by
  change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x = X.map (SimplexCategory.σ 0).op x
  exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ ↦ X.map α.op x) (Subsingleton.elim _ _)

/-- 概要：右 pinched 写像空間の零単体は指定された二頂点間の辺と同値。
方針：先頭面条件と最終頂点条件を始点・終点条件として読む。
規約：quasicategory 性は不要。
使われ方：HTT §1.2.2、Kerodon §4.6.5（Tag 01KW） の零単体と射の対応。 -/
def pinchedHomVertexEquiv {X : SSet.{u}} (x y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌ ≃ SSet.Truncated.Edge (X := (truncation 2).obj X) x y where
  toFun s :=
    { edge := s.val
      src_eq := by
        change X.map (SimplexCategory.δ (1 : Fin 2)).op s.val = x
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_zero, pinchedConstant_zero] using s.source
      tgt_eq := by
        change X.map (SimplexCategory.δ (0 : Fin 2)).op s.val = y
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex_zero] using s.target }
  invFun e :=
    { val := e.edge
      source := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_zero, pinchedConstant_zero]
        exact e.src_eq
      target := by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex_zero]
        exact e.tgt_eq }
  left_inv _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext rfl
  right_inv _ := SSet.Truncated.Edge.ext rfl

/-- 概要：右 pinched 写像空間の一次単体の面は元の三角形の最初の二面。
方針：最終点を固定する面写像の延長を有限順序集合で計算する。
規約：i は Fin 2。
使われ方：Kerodon §4.6.5（Tag 01KW） の辺とホモトピーの関係。 -/
lemma pinchedExtend_face_one (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
  fin_cases i <;> decide

/-- 概要：右 pinched 写像空間の辺は元の辺の右ホモトピーの三角形を与える。
方針：一次単体の先頭面と、写像空間の辺の両端を読む。
規約：三角形の後半の辺が終点、対角が始点の辺に対応する。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の連結成分への写像。 -/
def pinchedHomEdge_compStruct {X : SSet.{u}} {x y : X _⦋0⦌}
    {a b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌} (p : SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) a b) :
    SSet.Truncated.Edge.CompStruct (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x)
      (pinchedHomVertexEquiv x y b) (pinchedHomVertexEquiv x y a) where
  simplex := p.edge.val
  d₂ := by
    have h := p.edge.source
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ, pinchedConstant_one] at h
    exact h
  d₀ := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val p.tgt_eq
    change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (0 : Fin 2))).op p.edge.val = b.val at h
    rw [pinchedExtend_face_one] at h
    exact h
  d₁ := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val p.src_eq
    change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (1 : Fin 2))).op p.edge.val = a.val at h
    rw [pinchedExtend_face_one] at h
    exact h

/-- 概要：右 pinched 写像空間の連結成分をホモトピー圏の射に送る。
方針：零単体に対応する辺の類を取り、一次単体の合成三角形で well-defined 性を示す。
規約：この写像の構成には quasicategory 性は不要。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の π₀ と射の比較。 -/
def pinchedHomPiZeroToHom {X : SSet.{u}} (x y : X _⦋0⦌) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) → (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :=
  SSet.π₀.lift (fun s ↦ SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv x y s))
    (fun _ _ p ↦ by
      simpa using (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        (pinchedHomEdge_compStruct p)).symm)

/-- 概要：右ホモトピーの三角形は右 pinched 写像空間の一次単体を与える。
方針：先頭面が恒等辺である条件と、最終頂点の条件を確認する。
規約：f は後半の辺、g は対角。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の π₀ の単射性。 -/
def pinchedSimplexOfRightHomotopy {X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y 1 where
  val := t.simplex
  source := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ, pinchedConstant_one]
    exact t.d₂
  target := by
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 1 = SimplexCategory.δ (0 : Fin 2) ≫
        SimplexCategory.δ (0 : Fin 3) := by decide
    rw [h, op_comp, CategoryTheory.Functor.map_comp_apply]
    change X.δ 0 (X.δ 0 t.simplex) = y
    have h₀ : X.δ 0 t.simplex = f.edge := t.d₀
    rw [h₀]
    exact f.tgt_eq

/-- 概要：右ホモトピーから右 pinched 写像空間の辺を作る。
方針：三角形を一次単体にし、最初の二面を両端として読む。
規約：辺は g の頂点から f の頂点へ向く。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の同じ連結成分の証明。 -/
def pinchedHomEdgeOfRightHomotopy {X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (t : SSet.Truncated.Edge.CompStruct
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) f g) :
    SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) ((pinchedHomVertexEquiv x y).symm g)
      ((pinchedHomVertexEquiv x y).symm f) :=
  SSet.Edge.ofTruncated
    { edge := pinchedSimplexOfRightHomotopy t
      src_eq := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
        change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (1 : Fin 2))).op t.simplex = g.edge
        rw [pinchedExtend_face_one]
        exact t.d₁
      tgt_eq := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
        change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (0 : Fin 2))).op t.simplex = f.edge
        rw [pinchedExtend_face_one]
        exact t.d₀ }

/-- 概要：右 pinched 写像空間の連結成分からホモトピー圏の射への写像は単射。
方針：辺の類の等式を左ホモトピーに戻し、右ホモトピーから写像空間の辺を作る。
規約：仮定は X の quasicategory 性のみ。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の π₀ と射の一致。 -/
lemma pinchedHomPiZeroToHom_injective {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Injective (pinchedHomPiZeroToHom x y) := by
  intro a b h
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨t, rfl⟩ := SSet.π₀.mk_surjective b
  change SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv x y s) =
    SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv x y t) at h
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk (pinchedHomVertexEquiv x y s) =
      SSet.Truncated.HomotopyCategory₂.homMk (pinchedHomVertexEquiv x y t) := by
    have hh := congrArg (fun m ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj X)).map m) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL (pinchedHomVertexEquiv x y s)
      (pinchedHomVertexEquiv x y t) := Quotient.exact h₂
  obtain ⟨tri⟩ := SSet.Truncated.HomotopicL.homotopicR hh
  have hp := SSet.π₀.sound (pinchedHomEdgeOfRightHomotopy tri)
  simpa only [Equiv.symm_apply_apply] using hp.symm

/-- 概要：ホモトピー圏の任意の射は右 pinched 写像空間の連結成分から来る。
方針：A1 の比較により射を一本の辺で表し、対応する零単体の連結成分を取る。
規約：仮定は X の quasicategory 性のみ。
使われ方：HTT §1.2.3、Kerodon §4.6.5（Tag 01KW） の π₀ と射の一致。 -/
lemma pinchedHomPiZeroToHom_surjective {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : Function.Surjective (pinchedHomPiZeroToHom x y) := by
  intro f
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
  refine ⟨SSet.π₀.mk ((pinchedHomVertexEquiv x y).symm e), ?_⟩
  change SSet.Truncated.HomotopyCategory.homMk
    (pinchedHomVertexEquiv x y ((pinchedHomVertexEquiv x y).symm e)) = _
  rw [Equiv.apply_symm_apply]

/-- 概要：右 pinched 写像空間の連結成分はホモトピー圏の射と同値。
方針：辺の類への写像の単射性・全射性を組み合わせる。
規約：写像空間の Kan 性や別の模型との比較を追加仮定にしない。
使われ方：HTT §1.2.2–1.2.3、Kerodon §4.6.5（Tag 01KW）。 -/
noncomputable def pinchedHomPiZeroEquiv {X : SSet.{u}} [Quasicategory X]
    (x y : X _⦋0⦌) : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) ≃
      (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :=
  Equiv.ofBijective (pinchedHomPiZeroToHom x y)
    ⟨pinchedHomPiZeroToHom_injective x y, pinchedHomPiZeroToHom_surjective x y⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
