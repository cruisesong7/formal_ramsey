import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Presentation.Expr

open Lean Server
namespace ProofWidgets

structure PolygonSvgDisplayProps where
  svgHtml : String
  deriving RpcEncodable

@[widget_module]
def PolygonSvgDisplay : Component PolygonSvgDisplayProps where
  javascript := "import React from 'react';

const PolygonSvgDisplay = (props) => {
  // Create a props object for the div element
  const divProps = {
    dangerouslySetInnerHTML: { __html: props.svgHtml || '' }
  };

  // Return a React element for the div
  return React.createElement('div', divProps);
};

export default PolygonSvgDisplay;"


end ProofWidgets

open ProofWidgets Svg

def pi : Float := 3.141592653589793

def cos (angle : Float) : Float := Float.cos angle
def sin (angle : Float) : Float := Float.sin angle

def polygonVertex (sides : Nat) (radius centerX centerY : Float) (index : Nat) : (Float × Float) :=
  let angle : Float := 2.0 * pi * (Float.ofNat index / Float.ofNat sides)
  (centerX + radius * cos angle, centerY + radius * sin angle)

def polygonVertices (sides : Nat) (radius centerX centerY : Float) : Array (Float × Float) :=
  Array.mkArray sides (0.0, 0.0) |>.mapIdx (λ idx _ => polygonVertex sides radius centerX centerY idx)

def circleAtCoord (coord : Float × Float) : String :=
  let (cx, cy) := coord
  let r := 0.05  -- radius of the circle
  let strokeColor := "black"
  let strokeWidth := 0.01
  let fillColor := "white"
  s!"<circle cx='{cx}' cy='{cy}' r='{r}' stroke='{strokeColor}' stroke-width='{strokeWidth}' fill='{fillColor}' />\n"

def lineBetweenCoords (startCoord endCoord : Float × Float) (isRed : Bool) : String :=
  let (x1, y1) := startCoord
  let (x2, y2) := endCoord
  let strokeColor := "red" --if isRed then "red" else "blue"
  let strokeWidth := 0.02
  if isRed then
    ""
  else
    s!"<line x1='{x1}' y1='{y1}' x2='{x2}' y2='{y2}' stroke='{strokeColor}' stroke-width='{strokeWidth}' />\n"
def allVertexLines (vertices : Array (Float × Float)) (adjMatrix : Array (Array (Fin 2))) : List String :=
  let n := vertices.size
  List.join (List.range n |>.map (λ i =>
    List.range n |>.map (λ j =>
      if i < j then
        let isRed := adjMatrix[i]![j]! == (0 : Fin 2)
        some (lineBetweenCoords (vertices[i]!) (vertices[j]!) isRed)
      else none)
    |>.filterMap id))

def charToValue (c : Char) : Nat :=
  c.toNat - 63

def boolToFin2 (b : Bool) : Fin 2 :=
  if b then 1 else 0

def decodeG6Adjacency (s : String) (n : Nat) : Array (Array (Fin 2)) :=
  let bytes := s.toList.map charToValue
  let bits := bytes.foldl (λ acc b => acc ++ List.toArray (List.range 6 |>.map (λ i => boolToFin2 ((b) / (2 ^ (5 - i)) % 2 = 1)))) #[]
  let bitIdx (i j : Nat) : Nat := i * (i - 1) / 2 + j
  let emptyMatrix := Array.mkArray n (Array.mkArray n 0)
  emptyMatrix.mapIdx (λ i row =>
    row.mapIdx (λ j _ =>
      if i < j then
        if bitIdx j i < bits.size then bits.get! (bitIdx j i) else 0
      else if i = j then
        0
      else
        if bitIdx i j < bits.size then bits.get! (bitIdx i j) else 0))

def decodeG6 (s : String) : Array (Array (Fin 2)) :=
  let n := charToValue s.front
  decodeG6Adjacency (s.drop 1) n

private def frame : Frame where
  xmin   := -2
  ymin   := -2
  xSize  := 4
  width  := 400
  height := 400

def polygonSvg (g6 : String) : String :=
 let adjMat := decodeG6 g6
  let vertices := polygonVertices adjMat.size 1.5 0.0 0.0
  let vertexCircles := vertices.map circleAtCoord
  let vertexLines := allVertexLines vertices adjMat

  let svgElements := vertexCircles ++ vertexLines
  let svgContent := String.join svgElements.toList
  s!"<svg viewBox='-2 -2 4 4' xmlns='http://www.w3.org/2000/svg'>\n{svgContent}\n</svg>"

open ProofWidgets

@[expr_presenter]
def g6PolygonSvgPresenter : ExprPresenter where
  userName := "Polygon SVG Presenter"
  layoutKind := .inline
  present e :=
    match e with
    | Lean.Expr.lit (Lean.Literal.strVal g6String) =>
        let svgResult := polygonSvg g6String
        return Html.ofComponent PolygonSvgDisplay { svgHtml := svgResult } #[]
      | _ =>
        return Html.text "Please select a G6 string literal."

example : "GhdGKC".length > 0 := by
  with_panel_widgets [SelectionPanel]
    -- Users can select a G6 string literal in the goal panel.
  decide

-- [html verision]
-- def createCircleAtCoord (coord : Float × Float) : Element frame :=
--   circle coord (.abs 0.1) |>.setStroke (0., 0., 0.) (.px 2) |>.setFill (1., 1., 1.)

-- def createLineBetweenCoords (startCoord endCoord : Float × Float) (isRed : Bool) : Element frame :=
--   -- let strokeColor := if isRed then (1.0, 0.0, 0.0) else (0.0, 0.0, 1.0) -- Red or Blue
--   -- line startCoord endCoord |>.setStroke strokeColor (.px 2)
-- if isRed then
--   line startCoord endCoord |>.setStroke  (0.0, 0.0, 1.0) (.px 0)
-- else
--   line startCoord endCoord |>.setStroke  (0.0, 0.0, 1.0) (.px 2)

-- def createAllVertexLines (vertices : Array (Float × Float)) (adjMatrix : Array (Array (Fin 2))) : List (Element frame) :=
--   let n := vertices.size
--   List.join (List.range n |>.map (λ i =>
--     List.range n |>.map (λ j =>
--       if i < j then
--         let isRed := adjMatrix[i]![j]! == (0 : Fin 2)
--         some (createLineBetweenCoords (vertices[i]!) (vertices[j]!) isRed)
--       else none)
--     |>.filterMap id))

--#eval decodeG6 ("P}qTKukXaUja[IBjanPeMI\\K")
-- private def polygonSvg (g6 : String): Svg frame :=
--   let adjMat := decodeG6 g6
--   let vertices := regularPolygonVertices adjMat.size 1.5 0.0 0.0
--   let vertexCircles := vertices.map createCircleAtCoord
--   let vertexLines := createAllVertexLines vertices adjMat
--   { elements := Array.appendList vertexCircles vertexLines }

-- #html (polygonSvg "LhEIHEPQHGaPaP").toHtml
-- #html (polygonSvg "GhdGKC").toHtml
