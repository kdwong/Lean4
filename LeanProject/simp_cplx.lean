import Mathlib.Tactic -- standard proof tactics
import Mathlib.Data.Set.Defs -- basics on sets
import Mathlib.Data.Set.Finite.Basic -- basics on finite sets
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

@[simp]
def is_subset_closed {a : Type*} (S : Set (Finset a)) := ∀ s ∈ S, ∀ t, t ⊆ s →  t ∈ S

structure simplicial_complex (a : Type*) where
  simplices : Set (Finset a)
  subset_closed : is_subset_closed simplices


def vertices {a : Type*} (X : simplicial_complex a):
  Set a := { x : a | ∃ s ∈ X.simplices, x ∈ s }


def empty_sc {a : Type*} : simplicial_complex a :=
simplicial_complex.mk
(∅ : Finset (Finset a))
(by tauto)

@[simp]
def simplex {a : Type*} (V : Finset a): simplicial_complex a :=
simplicial_complex.mk
(Finset.powerset V)
      (by
      intro s hs t hsub
      exact Finset.mem_powerset.2 (Finset.Subset.trans hsub (Finset.mem_powerset.1 hs)))

@[simp]
def std_simplex (n : ℕ) : simplicial_complex ℕ := simplex (Finset.range (n+1))


@[simp]
def dim {a : Type*} (s : Finset a): ℕ := Finset.card s - 1

@[simp]
def has_dimension_leq {a : Type*} (X : simplicial_complex a) (n : ℕ)
:= ∀ s ∈  X.simplices, dim s ≤ n

@[simp]
def has_dimension_geq {a : Type*} (X : simplicial_complex a) (n : ℕ)
:= ∃ s ∈  X.simplices, dim s ≥ n

@[simp] def has_dimension {a : Type*} (X : simplicial_complex a) (n : ℕ)
:= has_dimension_leq X n ∧ has_dimension_geq X n

lemma dim_std_simplex (n : ℕ) : has_dimension (std_simplex n) n := by
constructor
· intro s hs
  have hsub : s ⊆ Finset.range (n+1) := Finset.mem_powerset.1 hs
  have hcard : Finset.card s ≤ Finset.card (Finset.range (n+1)) := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  simp [dim]
  exact hcard
· use Finset.range (n+1)
  simp [std_simplex, simplex]


@[simp]
def is_simplicial_map {a : Type*} {b : Type*} [DecidableEq b] (X : simplicial_complex a)
(Y : simplicial_complex b) (f : a → b)
:= ∀ s, s ∈  X.simplices →  Finset.image f s ∈ Y.simplices


structure simplicial_map
{a : Type*} {b : Type*} [DecidableEq b] (X : simplicial_complex a) (Y : simplicial_complex b) where
(map : a → b)
(is_simplicial : is_simplicial_map X Y map)

lemma vertex_to_singleton {a : Type*} (X : simplicial_complex a) (x : a) (x_in_X : x ∈ vertices X)
: {x} ∈  X.simplices := by
  -- Unfold the definition of `vertices` to get a simplex `s` containing `x`
  rcases x_in_X with ⟨s, hs, hx⟩
  -- Since `{x}` is a subset of `s`, the subset-closed property implies `{x} ∈ X.simplices`
  have h_subset : {x} ⊆ s := by simp [hx]
  exact X.subset_closed s hs {x} h_subset

lemma singleton_to_vertex {a : Type*} (X : simplicial_complex a) (x : a) (x_in_SX : {x} ∈ X.simplices): x ∈ vertices X := by
  -- Use the singleton `{x}` as the witness for the simplex containing `x`
  exact ⟨{x}, x_in_SX, by simp⟩

lemma simplicial_map_on_vertices {a : Type*} {b : Type*} [DecidableEq b] (X : simplicial_complex a) (Y : simplicial_complex b) (f : simplicial_map X Y) (x : a) (x_in_X : x ∈ vertices X)
: f.map x ∈ vertices Y := by
  have x_sing : {x} ∈ X.simplices := by apply vertex_to_singleton X x x_in_X
  have h_singleton : {f.map x} ∈ Y.simplices := by exact f.is_simplicial {x} x_sing
  apply singleton_to_vertex Y (f.map x) h_singleton

set_option linter.unusedVariables false in
lemma simplicial_map_dim_mono {a : Type*} {b : Type*} [DecidableEq b] (X : simplicial_complex a)
(Y : simplicial_complex b) (f : simplicial_map X Y) (s : Finset a) (s_in_SX : s ∈ X.simplices)
: dim (Finset.image f.map s) ≤ dim s := by
  simp only [dim]
  apply Nat.sub_le_sub_right
  exact Finset.card_image_le

lemma id_is_simplicial_map {a : Type*} [DecidableEq a] (X : simplicial_complex a) : is_simplicial_map X X (λ x : a => x) := by simp

set_option linter.unusedVariables false in
lemma const_is_simplicial {a : Type*} {b : Type*} [DecidableEq b] (X : simplicial_complex a)
(Y : simplicial_complex b) (y_0 : b) (y0_vertex : y_0 ∈ vertices Y) : is_simplicial_map X Y (λ x : a => y_0) := by
intro s hs
-- The image of any simplex under the constant function is either ∅ or {y_0}
by_cases h_empty : s = ∅
· rw [h_empty, Finset.image_empty]
  have : ∅ ∈ Y.simplices := by
    rcases y0_vertex with ⟨t, ht, _⟩
    exact Y.subset_closed t ht ∅ (Finset.empty_subset t)
  assumption
-- Case where s is non-empty, the image is {y_0}
· have h_image : Finset.image (λ x => y_0) s = {y_0} := by
    ext y
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · intro ⟨x, _, h⟩
      exact h.symm
    · intro h
      rw [h]
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h_empty
      exact ⟨x, hx, rfl⟩
  rw [h_image]
    -- We know {y_0} ∈ Y.simplices from y0_vertex
  exact vertex_to_singleton Y y_0 y0_vertex

def is_finite_simplicial_complex {a : Type*} (X : simplicial_complex a) := Set.Finite (X.simplices)

lemma fin_simplices_fin_vertices {a : Type*} (X : simplicial_complex a) (X_fin_S : is_finite_simplicial_complex X) : Set.Finite (vertices X) := by
  -- The vertices of X are the union of all elements in the simplices of X.
  -- Since X has finitely many simplices, and each simplex is a finite set,
  -- the union of all simplices is finite.
  have h : vertices X = ⋃ s ∈ X.simplices, (s : Set a) := by
    ext x -- ext changes A = B into x ∈ A <-> x ∈ B
    simp [vertices]
  rw [h]
  -- The union of finitely many finite sets is finite.
  apply Set.Finite.biUnion X_fin_S
  intro s y
  exact Finset.finite_toSet s


structure fin_simplicial_complex (a : Type*) where
(simplices : Finset (Finset a))
(subset_closed : is_subset_closed (simplices : Set (Finset a)))

def to_sc {a : Type*} (X : fin_simplicial_complex a) : simplicial_complex a
:= simplicial_complex.mk
(↑ X.simplices)
(X.subset_closed)

instance {a : Type*}: Coe (fin_simplicial_complex a) (simplicial_complex a) where coe := to_sc

lemma fin_sc_is_finite {a : Type*} (X : fin_simplicial_complex a): is_finite_simplicial_complex (↑ X : simplicial_complex a) := by
exact Finset.finite_toSet X.simplices


def fingen_simplices {a : Type*} [DecidableEq a] (S : Finset (Finset a))
: Finset (Finset a)
:= S.sup (λ x ↦ Finset.powerset x)


lemma fingen_simplices_sub_closed {a : Type*} [DecidableEq a] (S : Finset (Finset a))
: is_subset_closed (↑(fingen_simplices S) : Set (Finset a)) := by
  intro s hs t hsub
  -- Unfold the definition of `fingen_simplices` to understand `hs`
  simp only [fingen_simplices, Finset.mem_coe, Finset.mem_sup] at hs
  -- Obtain a simplex `x ∈ S` such that `s ∈ powerset x`
  rcases hs with ⟨x, hx, hs_powerset⟩
  -- Since `s ⊆ x` (from `s ∈ powerset x`) and `t ⊆ s`, we have `t ⊆ x`
  have htx : t ⊆ x := Finset.Subset.trans hsub (Finset.mem_powerset.1 hs_powerset)
  -- Thus, `t ∈ powerset x`
  have ht_powerset : t ∈ Finset.powerset x := Finset.mem_powerset.2 htx
  -- Since `x ∈ S`, this implies `t ∈ fingen_simplices S`
  simp only [fingen_simplices, Finset.mem_coe, Finset.mem_sup]
  exact ⟨x, hx, ht_powerset⟩
