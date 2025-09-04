# This is a python code for parametric optimization of the layout of spaces/classes(furniture and rooms). It consists of input of a
# set of furniture, their length, width, doorline position and travel line (a line from the closest point to one
# class' door-line to the other, offset at a given width from the edges of the classes in the visibility graph
# and optimized to be close to proximity weights as possible) between two pieces of furniture.
# The proximity values and privacy values would be input by the user for all pair combinations of spaces.
# A set of furniture enclosed in a concave hull form a room. The room class is therefore made up of all furniture whose
# function matches the function of the room. A room polygon will have a doorline and travel line to other rooms.
# A set of functional areas enclosed in a concave hull form a room. A room polygon has a doorline and travel line to
# other rooms. The code process is to read user data for the class of a space with defined furniture names, preset furniture
# dimensions, preset furniture door line and number of sides of the furniture with a doorline.The code ensures each
# furniture's coordinates meet the set lengths and widths, then sets furniture proximity values’ matrix, creates a concave hull
# of furniture points to form rooms, sets rooms proximity values' matrix, ensure furniture fit in the room and with an offset of
# 100mm from the edges of the room polygon, create a concave hull of functional areas’ points offset by 100mm for the room's wall
# ,sets door line user-given lengths fully on space edges, generate travel lines between spaces with proximity values and lastly
# optimizes the total area of the layout and the proximity values to meet the given weights.

import csv
import matplotlib.pyplot as plt
import numpy as np
from scipy.spatial import ConvexHull
from scipy.spatial import Delaunay
from scipy.optimize import minimize
from shapely.geometry import Polygon, Point, LineString, MultiLineString, MultiPolygon, MultiPoint, box, mapping
from shapely.ops import unary_union, polygonize
from shapely.geometry.polygon import orient
import random
import heapq
import math
import os
import alphashape
import itertools
import geojson
import ezdxf

# Define the boundaries of the graph
layout_width = 100  # Adjust as needed
layout_height = 100  # Adjust as needed
class Layout:
    def __init__(self, width, height):
        self.width = width
        self.height = height
        self.occupied_positions = [[False] * width for _ in range(height)]

    def mark_occupied(self, x, y):
        self.occupied_positions[y][x] = True

    def is_position_occupied(self, x, y):
        return self.occupied_positions[y][x]

    def is_position_valid(self, x, y):
        return not self.is_position_occupied(x, y)

layout = Layout(layout_width, layout_height)
# File path for the CSV file
csv_file_path = r'C:\Users\user\Downloads\furniture_data.csv'  # Using raw string to handle backslashes

#furniture class with the name, function, length, width, length of the door, width of the door,
#number of length doors and number of width door of the furniture
class Furniture:
    def __init__(self, furniture_name, function, length, width, length_door, width_door, num_length_door,
                 num_width_door):
        self.furniture_name = furniture_name
        self.function = function
        self.length = length
        self.width = width
        self.length_door = length_door
        self.width_door = width_door
        self.num_length_door = num_length_door
        self.num_width_door = num_width_door
        self.vertices = []  # Initialize vertices with an empty list
        self.doorlines = []  # Initialize offset door lines with an empty list
        self.offset_doorlines = []  # Initialize offset door lines with an empty list
        self.offset_polygon = None  # Initialize offset polygon with None
        self.room = None  # Initialize room attribute

    #function to generate random initial positions of funiture on the graph.
    def _generate_furniture_positions(self, furniture, graph_width, graph_height):
        initial_positions = []
        for _ in range(num_furniture):
            # Generate random position within the graph boundaries
            x = random.uniform(0, graph_width - furniture.length)  # Adjust to accommodate furniture dimensions
            y = random.uniform(0, graph_height - furniture.width)  # Adjust to accommodate furniture dimensions
            initial_positions.append((x, y))

        if initial_positions:  # Check if initial_positions is not empty
            furniture.vertices = initial_positions  # Populate the vertices attribute
            return initial_positions
        else:
            return []  # Return an empty list if initial_positions is empty

    def add_initial_position(self, positions):
        self.vertices.extend(positions)  # Use extend to add multiple vertices at once

    #function to generate offset polygon which will be used with visibility graph for the travel line for ensuring the
    #line is offset from furniture.
    distance = 0.6

    def generate_offset_polygon(self, distance):
        # Create a Shapely Polygon object from the furniture's vertices
        polygon = Polygon(self.vertices)
        # Offset the polygon by the given distance
        self.offset_polygon = polygon.buffer(distance)

    def clean_polygon(vertices):
    # Remove consecutive duplicate points
        cleaned = []
        seen = set()
        for v in vertices:
            if tuple(v) not in seen:
                cleaned.append(tuple(v))
                seen.add(tuple(v))
        return cleaned


    def generate_offset_lines(self):
        polygon = self.offset_polygon
        if polygon is None or polygon.is_empty:
            print(f"Offset polygon for object {getattr(self, 'room_name', getattr(self, 'furniture_name', 'unknown'))} is empty or None.")
        # Handle MultiPolygon by selecting the largest polygon
        if polygon.geom_type == 'MultiPolygon':
            # Pick the largest polygon
            largest = max(polygon.geoms, key=lambda p: p.area)
            polygon = largest
        offset_exterior_coords = list(polygon.exterior.coords)
        from shapely.geometry import box

    def generate_non_intersecting_position(furniture, occupied_polygons, layout_width, layout_height, max_attempts=100):
        for _ in range(max_attempts):
            x = random.uniform(0, layout_width - furniture.length)
            y = random.uniform(0, layout_height - furniture.width)

            # Create a polygon (box) for this furniture
            furn_poly = box(x, y, x + furniture.length, y + furniture.width)

            # Check intersection
            if all(not furn_poly.intersects(p) for p in occupied_polygons):
                return (x, y), furn_poly  # Valid position
        return None, None  # Failed

#function to read furniture data from csv file with given content in rows
def read_furniture_data_from_csv(csv_file):
    furniture_data = []
    with open(csv_file, 'r', newline='') as file:
        reader = csv.reader(file)
        next(reader)  # Skip header row
        for row in reader:
            furniture_name, function, length, width, length_door, width_door, num_length_door, num_width_door = row
            length = float(length)
            width = float(width)
            length_door = float(length_door)
            width_door = float(width_door)
            num_length_door = int(num_length_door)
            num_width_door = int(num_width_door)
            furniture_data.append(
                (furniture_name, function, length, width, length_door, width_door, num_length_door, num_width_door))
    return furniture_data

# Read furniture data from CSV file
furniture_data = read_furniture_data_from_csv(csv_file_path)

furniture_list = []
# Populate furniture_list with Furniture objects
for data in furniture_data:
    furniture = Furniture(*data)  # Create a Furniture object from the data
    furniture_list.append(furniture)  # Append the Furniture object to the list
offset_distance_furniture = 0.4

# Generate offset polygon and offset lines for each furniture
for furniture in furniture_list:
    furniture.generate_offset_polygon(offset_distance_furniture)
    furniture.generate_offset_lines()
# Create a mapping of furniture names to indices
furniture_names = [furniture.furniture_name for furniture in furniture_list]

num_furniture = len(furniture_names)

def is_valid_position(x, y,length, width, occupied_positions):
    # Check if the position overlaps with other occupied positions (furniture)
    for occupied_position in occupied_positions:
        if abs(x - occupied_position[0]) <length and abs(y - occupied_position[1]) < width:
            return False
    return True

# Room class with given objects
class Room:
    def __init__(self, room_name, functions, desired_ventilation_percentage, num_doorlines, vertices=None, furniture=None):
        if vertices is None:
            vertices = []
        if furniture is None:
            furniture = []
        self.room_name = room_name
        self.functions = functions.split(',')
        self.desired_ventilation_percentage = desired_ventilation_percentage
        self.num_doorlines = num_doorlines
        self.vertices = vertices if vertices is not None else [] # Store room boundary vertices
        self.furniture = furniture
        self.concave_hull = None  # Initialize concave hull attribute
        self.offset_polygon = None  # Initialize offset polygon with None
        self.offset_doorlines =[]

        def generate_offset_doorlines_rooms(self):
            if self.offset_polygon is None:
                print("Offset polygon is not generated. Call generate_offset_polygon method first.")
                return

            offset_doorlines = []
            # Convert the offset polygon's exterior coordinates to a list of tuples
            offset_exterior_coords = list(self.offset_polygon.exterior.coords)
            # Iterate over the exterior coordinates to create offset lines
            for i in range(len(offset_exterior_coords) - 1):
                offset_doorlines.append([offset_exterior_coords[i], offset_exterior_coords[i + 1]])
            # Assign the offset lines to the room's attribute
            self.offset_doorlines = offset_doorlines

    # Add a method to set room boundary vertices
    def set_vertices(self, vertices):
        self.vertices = vertices
    # function to generate offset polygon for generating visibility graph and travel lines ensuring line is offset from
    # room edges/wall
    # Create a Shapely Polygon object from the room's vertices
        polygon = Polygon(self.concave_hull)

    def add_furniture(self, furniture):
        self.furniture.append(furniture)

    def get_other_rooms(self, all_rooms):
        other_rooms = [room for room in all_rooms if room != self]
        return other_rooms

    #function to generate initial position of furniture in the room
    def generate_initial_positions(self, graph_width, graph_height, max_attempts=100):
        occupied_polygons = []  # Track placed furniture polygons

        for furniture in self.furniture:
            placed = False
            for attempt in range(max_attempts):
                # Random top-left corner position
                x = random.uniform(0, graph_width - furniture.length)
                y = random.uniform(0, graph_height - furniture.width)

                # Create a rectangular polygon for the furniture
                furniture_polygon = box(x, y, x + furniture.length, y + furniture.width)

                # Check for intersection with previously placed furniture
                if all(not furniture_polygon.intersects(p) for p in occupied_polygons):
                    # No intersection, place furniture
                    furniture.vertices = [
                        (x, y),
                        (x + furniture.length, y),
                        (x + furniture.length, y + furniture.width),
                        (x, y + furniture.width)
                    ]
                    occupied_polygons.append(furniture_polygon)
                    placed = True
                    break  # Exit attempt loop

            if not placed:
                print(f"[Error] Could not place furniture '{furniture.furniture_name}' in room '{self.room_name}' after {max_attempts} attempts.")

        # Update room vertices from placed furniture
        self.update_vertices()

    def update_vertices(self):
        self.vertices = [vertex for furniture in self.furniture for vertex in furniture.vertices]

    def collect_furniture_vertices(self):
        furniture_vertices = []
        for furniture in self.furniture:
            # Convert vertices to NumPy array for consistency
            vertices_array = np.array(furniture.vertices)
            furniture_vertices.append(vertices_array)
        return furniture_vertices
    #function to generate doorlines along furniture lengths and widths
    def generate_doorlines(self, num_length_doors, num_width_doors):
        doorlines = []
        for furniture in self.furniture:
            # Create LineString object from furniture vertices
            furniture_line = LineString(furniture.vertices)
            # Generate doorlines along the lengths of the furniture
            length_doorlines = self._generate_doorlines_along_length(furniture_line, num_length_doors)
            # Generate doorlines along the widths of the furniture
            width_doorlines = self._generate_doorlines_along_width(furniture_line, num_width_doors)
            # Extend the list of doorlines
            doorlines.extend(length_doorlines)
            doorlines.extend(width_doorlines)
            # Assign the doorlines to the furniture's attribute
            furniture.doorlines = doorlines
        return doorlines

    def _generate_doorlines_along_length(self, line, num_length_doors):
        doorlines = []
        # Interpolate points along the LineString to generate doorline vertices for length doors
        interpolated_points = [line.interpolate(i / (num_length_doors + 1), normalized=True) for i in
                               range(num_length_doors)]
        # Generate doorlines for length doors
        for i in range(num_length_doors):
            start_point = (interpolated_points[i].x, interpolated_points[i].y)
            end_point = (interpolated_points[i + 1].x, interpolated_points[i + 1].y)
            doorlines.append([start_point, end_point])
        return doorlines

    def _generate_doorlines_along_width(self, line, num_width_doors):
        doorlines = []
        # Get the centroid of the LineString
        centroid = line.centroid
        # Calculate the normal vector to the LineString
        normal_vector = (line.coords[1][1] - line.coords[0][1], -(line.coords[1][0] - line.coords[0][0]))
        # Generate doorlines along the width of the furniture
        for i in range(num_width_doors):
            # Calculate the offset point from the centroid in the direction of the normal vector
            offset_point = (centroid.x + normal_vector[0] * (i + 1), centroid.y + normal_vector[1] * (i + 1))
            # Extend the doorline from the offset point along the normal vector
            start_point = (offset_point[0] - normal_vector[0], offset_point[1] - normal_vector[1])
            end_point = (offset_point[0] + normal_vector[0], offset_point[1] + normal_vector[1])
            doorlines.append([start_point, end_point])
        return doorlines

    def generate_offset_lines(self):
        if self.offset_polygon is None:
            print("Offset polygon is not generated. Call generate_offset_polygon method first.")
            return

        offset_doorlines = []
        # Convert the offset polygon's exterior coordinates to a list of tuples
        offset_exterior_coords = list(self.offset_polygon.exterior.coords)
        # Iterate over the exterior coordinates to create offset lines
        for i in range(len(offset_exterior_coords) - 1):
            offset_doorlines.append([offset_exterior_coords[i], offset_exterior_coords[i + 1]])
        # Assign the offset lines to the room's attribute
        self.offset_lines = offset_doorlines

    #function to generate offset doorlines since travel lines start at offset doorlines.
    def generate_offset_doorlines(self, doorlines, offset_distance):
        offset_doorlines = []
        for doorline in doorlines:
            # Create LineString object from doorline vertices
            doorline_line = LineString(doorline)
            # Calculate the normal vector to the doorline
            normal_vector = (doorline_line.coords[1][1] - doorline_line.coords[0][1],
                             -(doorline_line.coords[1][0] - doorline_line.coords[0][0]))
            # Calculate offset points along the normal vector
            offset_point1 = (
            doorline[0][0] + normal_vector[0] * offset_distance, doorline[0][1] + normal_vector[1] * offset_distance)
            offset_point2 = (
            doorline[1][0] + normal_vector[0] * offset_distance, doorline[1][1] + normal_vector[1] * offset_distance)
            # Append the offset doorline
            offset_doorlines.append([offset_point1, offset_point2])
        return offset_doorlines
    
    
    def generate_offset_doorlines_rooms(self):
        if self.offset_polygon is None:
            print("Offset polygon is not generated. Call generate_offset_polygon method first.")
            return
        
        num_doorlines = room.num_doorlines
        rooms_offset_doorlines = []

        # Generate doorlines for the room
        for _ in range(num_doorlines):
            # Generate random points along the room boundary
            point_on_boundary = random.choice(self.offset_polygon.exterior.coords)
            # Calculate a second point for the doorline by moving along the boundary
            second_point = self.offset_polygon.exterior.interpolate( offset_distance, normalized=True)
            doorline = [point_on_boundary, (second_point.x, second_point.y)]
            rooms_offset_doorlines.append(doorline)

        # Assign the offset doorlines to the room's attribute
        self.offset_doorlines = rooms_offset_doorlines
        return rooms_offset_doorlines

    def generate_offset_polygon(self, buffer_distance=1.0):
        if not self.furniture:
            print(f"[Error] Room {self.room_name} has no furniture assigned.")
            return

        all_points = []
        for f in self.furniture:
            all_points.extend(f.vertices)

        if not all_points:
            print(f"[Error] Room {self.room_name} has no vertices from furniture.")
            return

        self.concave_hull = create_concave_hull(all_points, alpha=1.0)
        if self.concave_hull is None or self.concave_hull.is_empty:
            print(f"[Fallback] Concave hull not valid for room {self.room_name}. Using convex hull.")
            self.concave_hull = MultiPoint(all_points).convex_hull

        try:
            buffered = self.concave_hull.buffer(buffer_distance)
            if buffered.geom_type == 'MultiPolygon':
                self.offset_polygon = max(buffered.geoms, key=lambda p: p.area)
            else:
                self.offset_polygon = buffered

            if self.offset_polygon.is_empty:
                print(f"[Error] Offset polygon for room {self.room_name} is empty.")
            else:
                print(f"[OK] Room {self.room_name} offset polygon generated.")
        except Exception as e:
            print(f"[Error] Failed to generate offset polygon for room {self.room_name}: {e}")
    
def check_room_intersections(rooms):
    for i, room1 in enumerate(rooms):
        for j, room2 in enumerate(rooms):
            if i >= j: continue  # avoid duplicate checks
            poly1 = room1.offset_polygon
            poly2 = room2.offset_polygon
            if poly1 and poly2 and poly1.intersects(poly2):
                print(f"[Conflict] Offset polygons intersect between {room1.room_name} and {room2.room_name}")

furniture_vertices = []
for furn in furniture_list:
    furniture_vertices.extend(furn.vertices)  # vertices should be (x, y)

def create_concave_hull(points, alpha=1.0):
    if len(points) < 4:
        print("[Warning] Not enough points for a concave hull. Returning convex hull or point set.")
        return MultiPoint(points).convex_hull
    try:
        concave = alphashape.alphashape(points, alpha)
        if concave.is_empty or not concave.is_valid:
            raise ValueError("Concave hull is empty or invalid")
        return concave
    except Exception as e:
        print(f"[Fallback] Alphashape failed: {e}. Using convex hull.")
        return MultiPoint(points).convex_hull

concave_hull = create_concave_hull(furniture_vertices, alpha=1.0)
#function to collect all points in a room including furniture vertices and travel lines
def collect_room_points(room, travel_lines):
    points = []
    # Add all furniture vertices for this room
    for f in room.furniture:
        points.extend(f.vertices)
    # Add all travel line endpoints for this room
    for line in travel_lines:
        if room.room_name in line.get('rooms', []):
            points.append(tuple(line['start']))
            points.append(tuple(line['end']))
    # Remove duplicates
    points = [tuple(map(float, p)) for p in points]
    points = list(set(points))
    return points

#function to read rooms from csv file with given objects
def read_rooms_from_csv(csv_file):
    rooms = []
    with open(csv_file, 'r', newline='') as file:
        reader = csv.reader(file)
        next(reader)  # Skip header row
        for row in reader:
            if len(row) >= 5:
                room_name, functions, desired_ventilation_percentage, num_doorlines, vertices_data = row
            else:
                room_name, functions, desired_ventilation_percentage, num_doorlines = row
                vertices_data = ''  # Set vertices data to empty string if not present
            desired_ventilation_percentage = float(desired_ventilation_percentage)

            # Convert num_doorlines to integer
            num_doorlines = int(num_doorlines)

            # Convert vertices_data to list of tuples if it's not an empty string
            if vertices_data:
                vertices = [tuple(map(float, point.split(','))) for point in vertices_data.split(';')]
            else:
                vertices = []  # Set vertices to an empty list if vertices_data is an empty string
            room = Room(room_name, functions, desired_ventilation_percentage, num_doorlines, vertices=vertices)
            rooms.append(room)
    return rooms

def print_csv_file(file_path):
    with open(file_path, 'r', newline='') as file:
        reader = csv.reader(file)
        for row in reader:
            print(row)

# Print contents of furniture data CSV file
print("Furniture Data:")
print_csv_file(csv_file_path)

# File path for the CSV file
csv_file_path2 = r'C:\Users\user\Downloads\rooms_data.csv'  # Adjust the file path accordingly
# Print contents of rooms data CSV file
print("\nRooms Data:")
print_csv_file(csv_file_path2)

def clean_polygon(vertices):
    """Remove consecutive or duplicate points from a list of vertices."""
    cleaned = []
    seen = set()
    for v in vertices:
        key = tuple(v)
        if key not in seen:
            cleaned.append(key)
            seen.add(key)
    return cleaned

# Read rooms data from CSV file
rooms = read_rooms_from_csv(csv_file_path2)
#Group furniture by their functions and assign them to rooms
# Assign furniture to rooms based on matching functions
for room in rooms:
    for furniture in furniture_list:
        if furniture.function.strip().lower() in [func.strip().lower() for func in room.functions]:
            room.add_furniture(furniture)

# (your existing imports and class definitions remain unchanged)

# STEP 1: Assign furniture to rooms based on matching function
for room in rooms:
    for furniture in furniture_list:
        if furniture.function in room.functions:
            room.add_furniture(furniture)

# STEP 2: Generate non-overlapping furniture positions within the layout space
for room in rooms:
    room.generate_initial_positions(layout_width, layout_height)
    room.update_vertices()  # Update room.vertices with furniture points

# STEP 3: Generate concave hull from furniture positions
for room in rooms:
    if not room.vertices:
        print(f"[Error] Room {room.room_name} has no vertices from furniture.")
        continue
    room.concave_hull = create_concave_hull(room.vertices, alpha=1.0)

# STEP 4: Generate offset polygon
for room in rooms:
    room.generate_offset_polygon(buffer_distance=1.0)

# Optional: Print debug info
for room in rooms:
    print(f"[Info] Room {room.room_name} has {len(room.furniture)} furniture items.")
    if room.offset_polygon:
        print(f"[OK] Offset polygon generated for room {room.room_name}.")
    else:
        print(f"[Error] Offset polygon for room {room.room_name} not generated.")

            
for room in rooms:
    room.generate_offset_polygon(buffer_distance=0.2)

for room in rooms:
    if room.offset_polygon:
        print(list(room.offset_polygon.exterior.coords))
    else:
        print(f"[Error] Offset polygon for room {room.room_name} not generated.")

generate_offset_lines = Room.generate_offset_lines
offset_distance = 1.1
print(f"[Info] Room {room.room_name} has {len(room.furniture)} furniture items.")

# Generate offset polygon and offset lines for each room
for room in rooms:
    room.generate_offset_polygon(offset_distance)
    room.generate_offset_lines()
    room.generate_doorlines

# function to constrain length and width during optimization
def constrain_length_width(vertices, length, width):
    adjusted_vertices = []

    # Ensure vertices list is not empty
    if vertices:
        # Adjust the position of the second vertex to meet the length constraint
        adjusted_vertices.append(vertices[0])  # Vertex 1 remains unchanged
        adjusted_vertices.append((vertices[0][0] + length, vertices[0][1]))  # Vertex 2 adjusted

        # Adjust the position of the third vertex to meet the width constraint
        adjusted_vertices.append((adjusted_vertices[1][0], adjusted_vertices[1][1] + width))  # Vertex 3 adjusted

        # Adjust the position of the fourth vertex to meet the width constraint
        adjusted_vertices.append((adjusted_vertices[0][0], adjusted_vertices[0][1] + width))  # Vertex 4 adjusted

    return adjusted_vertices

# Create a 2D array for proximity values
proximity_matrix_furniture = [[0.0] * num_furniture for _ in range(num_furniture)]
# Prompt for proximity values between furniture items

print("Please provide proximity values between furniture items:")
for i in range(num_furniture):
    for j in range(i + 1, num_furniture):
        try:
            proximity = float(input(f"Enter the proximity value between {furniture_names[i]} and {furniture_names[j]} (in meters): "))
        except ValueError as e:
            print(f"[Input Error] Could not parse proximity between {furniture_names[i]} and {furniture_names[j]}: {e}")
            proximity = 1.0  # fallback default

        proximity_matrix_furniture[i][j] = proximity
        proximity_matrix_furniture[j][i] = proximity

# Print the proximity matrix for furniture items
print("\nProximity Matrix for furniture items:")
for row in proximity_matrix_furniture:
    print(row)

# File path for the CSV file
csv_file_path2 = r'C:\Users\user\Downloads\rooms_data.csv'  # Adjust the file path accordingly

# Read rooms data from CSV file
rooms = read_rooms_from_csv(csv_file_path2)

def read_rooms_data_from_csv(csv_file):
    rooms_data = []
    with open(csv_file, 'r', newline='') as file:
        reader = csv.reader(file)
        next(reader)  # Skip header row
        for row in reader:
            room_name, functions, desired_ventilation_percentage, num_doorlines = row
            desired_ventilation_percentage = float(desired_ventilation_percentage)
            rooms_data.append(
                (room_name, functions, desired_ventilation_percentage, num_doorlines))
    return rooms_data

num_rooms = len(rooms)
proximity_matrix_rooms = [[0.0] * num_rooms for _ in range(num_rooms)]

# Prompt for proximity values between rooms
print("\nPlease provide proximity values between rooms:")

for i in range(num_rooms):
    for j in range(i + 1, num_rooms):  # Start from i + 1 to avoid duplicate pairs
        room1 = rooms[i].room_name
        room2 = rooms[j].room_name
        proximity = float(input(f"Enter the proximity value between {room1} and {room2} (in meters): "))
        proximity_matrix_rooms[i][j] = proximity
        proximity_matrix_rooms[j][i] = proximity

# Print the proximity matrix for rooms
print("\nProximity Matrix for rooms:")
for row in proximity_matrix_rooms:
    print(row)
    
# Print the generated offset polygon
print(f"Generated offset polygon for room {room.room_name}:")
print(room.offset_polygon)
# Print the exterior coordinates of the offset polygon
print(f"Offset polygon for room {room.room_name}:")
if room.offset_polygon.geom_type == 'MultiPolygon':
    largest = max(room.offset_polygon.geoms, key=lambda p: p.area)
    print(f"[MultiPolygon] Room {room.room_name}:")
    print(list(largest.exterior.coords))
elif room.offset_polygon.geom_type == 'Polygon':
    print(f"[Polygon] Room {room.room_name}:")
    print(list(room.offset_polygon.exterior.coords))
else:
    print(f"[Error] Room {room.room_name} has unsupported geometry type: {room.offset_polygon.geom_type}")


# Define the Graph class
class Graph:
    def __init__(self):
        self.vertices = {}

    def add_vertex(self, vertex):
        self.vertices[vertex] = []

    def add_edge(self, vertex1, vertex2):
        self.vertices[vertex1].append(vertex2)
        self.vertices[vertex2].append(vertex1)

offset_doorlines_graph = {}

# Construct the offset doorlines graph
for room in rooms:
    for doorline in room.offset_doorlines:
        offset_doorlines_graph[doorline] = []  # Initialize empty list of neighbors

def euclidean_distance(point1, point2):
    x1, y1 = point1
    x2, y2 = point2
    return math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)

threshold_distance = 0.2
# Populate the neighbors of each offset doorline for the visibility graph
for doorline in offset_doorlines_graph:
    for other_doorline in offset_doorlines_graph:
        if doorline != other_doorline:  # Exclude self-connections
            # Check if the doorlines are close enough to be considered neighbors
            if euclidean_distance(doorline[0], other_doorline[0]) < threshold_distance:
                offset_doorlines_graph[doorline].append(other_doorline)
            if euclidean_distance(doorline[1], other_doorline[1]) < threshold_distance:
                offset_doorlines_graph[doorline].append(other_doorline)
# Function to compute the visibility graph furniture from furniture vertices
def compute_visibility_graph_furniture(furniture_list):
    visibility_graph_furniture = {}

    # Compute visibility between all pairs of furniture items within the same room
    for room in rooms:
        room_furniture = [furniture for furniture in furniture_list if furniture.room == room]
        for i, furniture1 in enumerate(room_furniture):
            for j, furniture2 in enumerate(room_furniture):
                if i != j:  # Skip comparing a piece of furniture with itself
                    visibility_line = LineString([furniture1.vertices[0], furniture2.vertices[0]])
                    intersects = False
                    for furniture in room_furniture:
                        if furniture != furniture1 and furniture != furniture2:
                            if furniture.offset_polygon.intersects(visibility_line):
                                intersects = True
                                break
                    # If the line segment does not intersect with any other furniture, add it to the visibility graph
                    if not intersects:
                        if furniture1 in visibility_graph_furniture:
                            visibility_graph_furniture[furniture1].append(furniture2)
                        else:
                            visibility_graph_furniture[furniture1] = [furniture2]

    return visibility_graph_furniture

# Define a function to compute the visibility graph for rooms from room vertices.
def compute_visibility_graph_rooms(rooms):
    visibility_graph_rooms = {}

    # Compute visibility between all pairs of rooms
    for room1 in rooms:
        for room2 in rooms:
            if room1 != room2:
                if room1.vertices and room2.vertices:  # Check if vertices are not empty
                    # Create LineString using the vertices of the rooms
                    visibility_line = LineString([room1.vertices[0], room2.vertices[0]])
                    intersects = False
                    for room in rooms:
                        if room != room1 and room != room2:
                            if room.offset_polygon.intersects(visibility_line):
                                intersects = True
                                break
                    # If the line segment does not intersect with any other room, add it to the visibility graph
                    if not intersects:
                        if room1 in visibility_graph_rooms:
                            visibility_graph_rooms[room1].append(room2)
                        else:
                            visibility_graph_rooms[room1] = [room2]

    return visibility_graph_rooms

# Compute visibility graph for furniture
visibility_graph_furniture = compute_visibility_graph_furniture(furniture_list)

# Compute visibility graph for rooms
visibility_graph_rooms = compute_visibility_graph_rooms(rooms)

#function to calculate cost of travel line using A* algorithm
def a_star(graph, start, goal):
    pq = [(0, start)]
    visited = set()
    parents = {start: None}
    costs = {start: 0}

    curr = None
    while pq:
        cost, curr = heapq.heappop(pq)
        if curr == goal:
            break

        visited.add(curr)
        for neighbor in graph[curr]:
            new_cost = costs[curr] + euclidean_distance(curr, neighbor)
            if neighbor not in costs or new_cost < costs[neighbor]:
                costs[neighbor] = new_cost
                parents[neighbor] = curr
                heapq.heappush(pq, (new_cost + euclidean_distance(neighbor, goal), neighbor))

    path = []
    while curr:
        path.append(curr)
        curr = parents[curr]
    path.reverse()
    return path

def gather_start_goal_vertices(rooms):
    all_start_goal_vertices_rooms = set()
    for room1 in rooms:
        for furniture1 in room1.furniture:
            if furniture1.furniture_name.lower() == "lobby":
                for doorline1 in furniture1.offset_doorlines:
                    start_vertex = doorline1[0]
                    goal_vertex = doorline1[1]
                    all_start_goal_vertices_furniture.add(start_vertex)
                    all_start_goal_vertices_furniture.add(goal_vertex)
        for room2 in rooms:
            if room1 != room2:
                for furniture2 in room2.furniture:
                    if furniture2.furniture_name.lower() == "lobby":
                        for doorline2 in furniture2.offset_doorlines:
                            start_vertex = doorline2[0]
                            goal_vertex = doorline2[1]
                            all_start_goal_vertices_rooms.add(start_vertex)
                            all_start_goal_vertices_rooms.add(goal_vertex)
    return all_start_goal_vertices_rooms

# Call the function to gather start and goal vertices
all_start_goal_vertices_rooms = gather_start_goal_vertices(rooms)

def gather_visibility_vertices(graph):
    all_visibility_vertices = set()
    for vertex, neighbors in graph.items():
        all_visibility_vertices.add(vertex)
        all_visibility_vertices.update(neighbors)
    return all_visibility_vertices

def gather_visibility_vertices_rooms(visibility_graph_rooms):
    all_visibility_vertices_rooms = set()
    for vertex, neighbors in visibility_graph_rooms.items():
        all_visibility_vertices_rooms.add(vertex)
        all_visibility_vertices_rooms.update(neighbors)
    return all_visibility_vertices_rooms

def generate_graph(vertices):
    graph = {vertex: [] for vertex in vertices}
    for vertex in vertices:
        for neighbor in graph:
            if neighbor != vertex:
                # Check if there is a direct path between the current vertex and the neighbor
                # This check should be based on the conditions of your problem
                # if is_direct_path(vertex, neighbor):  # Implement is_direct_path based on your problem
                graph[vertex].append(neighbor)
                graph[neighbor].append(vertex)
    return graph

# Gather start and goal vertices for furniture
all_start_goal_vertices_furniture = gather_start_goal_vertices(rooms)

# Gather visibility vertices for furniture and rooms
all_visibility_vertices_furniture = gather_visibility_vertices(visibility_graph_furniture)
all_visibility_vertices_rooms = gather_visibility_vertices(visibility_graph_rooms)

# Combine start, goal, and visibility graph vertices for furniture and rooms
all_vertices_furniture = all_visibility_vertices_furniture.union(all_start_goal_vertices_furniture)
all_vertices_rooms = all_visibility_vertices_rooms.union(all_start_goal_vertices_rooms)

# Generate graph for furniture and rooms
graph_furniture = generate_graph(all_vertices_furniture)
graph_rooms = generate_graph(all_vertices_rooms)

# functions to find travel lines using visibility graph and A* algorithm
def find_travel_lines_between_furniture(furniture_list, graph_furniture):
    travel_lines_between_furniture = {}

    # Iterate over each pair of furniture items
    for furniture1 in furniture_list:
        for furniture2 in furniture_list:
            if furniture1 != furniture2:
                # Choose either vertex as start or goal
                for start_vertex in furniture1.offset_doorlines:
                    for goal_vertex in furniture2.offset_doorlines:
                        # Find the shortest path between start and goal vertices using the visibility graph
                        shortest_path = a_star(graph_furniture, start_vertex, goal_vertex)

                        # Convert the shortest path to a LineString
                        shortest_line = LineString(shortest_path)

                        # Add the shortest line between the two furniture items to the travel lines dictionary
                        travel_lines_between_furniture[(furniture1, furniture2, start_vertex, goal_vertex)] = shortest_line

    return travel_lines_between_furniture

def find_travel_lines_between_rooms(rooms, graph_rooms):
    travel_lines_between_rooms = {}

    # Iterate over each pair of rooms
    for room1 in rooms:
        for room2 in rooms:
            if room1 != room2:
                # Choose either vertex as start or goal
                for start_vertex in room1.offset_doorlines:
                    for goal_vertex in room2.offset_doorlines:
                        # Find the shortest path between start and goal vertices using the visibility graph
                        shortest_path = a_star(graph_rooms, start_vertex, goal_vertex)

                        # Convert the shortest path to a LineString
                        shortest_line = LineString(shortest_path)

                        # Add the shortest line between the two rooms to the travel lines dictionary
                        travel_lines_between_rooms[(room1, room2, start_vertex, goal_vertex)] = shortest_line

    return travel_lines_between_rooms


# Compute travel lines between furniture
travel_lines_between_furniture = find_travel_lines_between_furniture(furniture_list, graph_furniture)

# Print travel lines between furniture
print("Travel lines between furniture:")
for key, value in travel_lines_between_furniture.items():
    print(f"Travel line between {key[0].furniture_name} and {key[1].furniture_name}: {value}")

# Find travel lines between rooms
travel_lines_between_rooms = find_travel_lines_between_rooms(rooms, graph_rooms)

# Print travel lines between rooms
print("\nTravel lines between rooms:")
for room_pair, line_between_rooms in travel_lines_between_rooms.items():
    print(f"Travel line between {room_pair[0].room_name} and {room_pair[1].room_name}: {line_between_rooms}")

# Modify the code where rooms are read from CSV to include other rooms
def main():
    # File path for the CSV file
    csv_file_path2 = r'C:\Users\user\Downloads\rooms_data.csv'  # Adjust the file path accordingly

    # Read rooms data from CSV file
    rooms = read_rooms_from_csv(csv_file_path2)

    # Iterate through each room to process
    for room in rooms:
        # Get other rooms excluding the current room
        other_rooms = room.get_other_rooms(rooms)

        # Now you can pass other_rooms to any method that requires it, such as calculate_ventilation_walls
        # e.g., room.calculate_ventilation_walls(other_rooms)

        # Example usage:
        print(f"Other rooms in the layout for room {room.room_name}:")
        for other_room in other_rooms:
            print(other_room.room_name)

if __name__ == "__main__":
    main()
    #function to calculate ventilation walls which lack obstruction at a given distance outwards
    def calculate_centroid(self):
        num_vertices = len(self.vertices)
        centroid_x = sum(vertex[0] for vertex in self.vertices) / num_vertices
        centroid_y = sum(vertex[1] for vertex in self.vertices) / num_vertices
        return centroid_x, centroid_y

    def calculate_ventilation_walls(self):
        num_walls = len(self.vertices)
        ventilation_walls = []

        centroid_x, centroid_y = self.calculate_centroid()

        for i in range(num_walls):
            wall_start = np.array(self.vertices[i])
            wall_end = np.array(self.vertices[(i + 1) % num_walls])
            wall_vector = wall_end - wall_start
            wall_length = np.linalg.norm(wall_vector)

            # Calculate perpendicular vector
            perpendicular_vector = np.array([-wall_vector[1], wall_vector[0]], dtype=float)
            perpendicular_vector /= np.linalg.norm(perpendicular_vector)

            # Determine direction of projection based on the position relative to the centroid
            wall_midpoint = (wall_start + wall_end) / 2
            centroid_direction = np.array([centroid_x - wall_midpoint[0], centroid_y - wall_midpoint[1]])
            projection_direction = np.sign(np.dot(centroid_direction, perpendicular_vector))
            line_segment_end = wall_midpoint + perpendicular_vector * projection_direction * 6.0

            # Calculate the length of the line segment meeting the ventilation constraint
            segment_length = np.linalg.norm(line_segment_end - wall_midpoint)

            # Calculate the percentage of the wall meeting the ventilation constraint
            ventilation_percentage = (segment_length / wall_length) * 100

            ventilation_walls.append(ventilation_percentage)

        return ventilation_walls

    def calculate_ventilation_percentage(self):
        return sum(self.ventilation_walls) / len(self.ventilation_walls)

    def ventilation_constraint(self, allowance=0):
        return self.ventilation_percentage - (self.desired_ventilation_percentage + allowance)


def shoelace_formula(x_y):
    x_y = np.array(x_y)
    x_y = x_y.reshape(-1, 2)
    x = x_y[:, 0]
    y = x_y[:, 1]
    S1 = np.sum(x * np.roll(y, -1))
    S2 = np.sum(y * np.roll(x, -1))
    area = 0.5 * np.abs(S1 - S2)
    return area

def area_of_outer_polygon_with_holes(outer_polygon_vertices, inner_holes):
    outer_area = shoelace_formula(outer_polygon_vertices)
    for hole in inner_holes:
        hole_area = shoelace_formula(hole)
        outer_area -= hole_area
    return outer_area

def total_area_objective(outer_polygons_with_holes):
    total_area = 0.0
    for outer_polygon, inner_holes in outer_polygons_with_holes:
        total_area += area_of_outer_polygon_with_holes(outer_polygon, inner_holes)
    return total_area

#computation of total area of polygon given shape and holes boundaries
##outer_polygons_with_holes = [([outer_polygon_vertices], [hole1_vertices, hole2_vertices])]
##inner_holes = (hole1_vertices, hole2_vertices)
##total_area = total_area_objective(outer_polygons_with_holes)

def calculate_angle(vector1, vector2):
    """
    Calculates the angle in radians between two vectors.
    """
    # Ensure vectors are normalized to avoid numerical errors
    vector1 = vector1 / np.linalg.norm(vector1)
    vector2 = vector2 / np.linalg.norm(vector2)

    # Calculate the dot product
    dot_product = np.dot(vector1, vector2)

    # Ensure the dot product is within [-1, 1] to avoid invalid input to arccos
    dot_product = np.clip(dot_product, -1.0, 1.0)

    # Calculate the angle using the arccosine function
    angle = np.arccos(dot_product)

    return angle

# function to create shape of polygon
def main():
    # Get the number of sides of the outer polygon from the user
    num_sides = int(input("Enter the number of sides of the outer polygon: "))

    # Initialize a list to store the desired counterclockwise angles for each side
    desired_angles = []

    # Get the desired counterclockwise angle for each side of the polygon
    for i in range(num_sides):
        angle_degrees = float(input(f"Enter the desired counterclockwise angle (in degrees) for side {i + 1}: "))
        desired_angles.append(np.radians(angle_degrees))

    print("Desired angles for the outer polygon (in radians):", desired_angles)

    # Calculate the angles between consecutive sides based on the desired angles
    angles = []
    for i in range(num_sides):
        vector1 = np.array([np.cos(desired_angles[i]), np.sin(desired_angles[i])])
        vector2 = np.array([np.cos(desired_angles[(i + 1) % num_sides]), np.sin(desired_angles[(i + 1) % num_sides])])
        angle = calculate_angle(vector1, vector2)
        angles.append(angle)

    print("Calculated angles between consecutive sides (in radians):", angles)

    # Convert the first angle to degrees for easier understanding
    print("First angle between sides (in degrees):", np.degrees(angles[0]))

# Usage example
vector1 = np.array([1, 0])
vector2 = np.array([0, 1])
angle = calculate_angle(vector1, vector2)
print(np.degrees(angle))  # Convert angle from radians to degrees

def angle_size_constraint(x, num_sides, desired_angles):
    # Calculate the angles between consecutive segments based on the optimization variables x
    angles = calculate_angle(x)
    # Calculate the desired angle size based on the original polygon shape
    desired_angle_size = calculate_angle(desired_angles)
    # Check if the angles deviate significantly from the desired angle size
    angle_deviations = [abs(angle - desired_angle_size) for angle in angles]
    max_deviation = 0.1  # Maximum allowed deviation from the desired angle size
    violated_angles = [deviation for deviation in angle_deviations if deviation > max_deviation]
    return sum(violated_angles)  # Return the sum of deviations

class Layout:
    def __init__(self, width, height):
        self.width = width
        self.height = height
        self.occupied_positions = [[False] * width for _ in range(height)]  # Grid to track occupied positions

    def mark_occupied(self, x, y):
        self.occupied_positions[y][x] = True

    def is_position_occupied(self, x, y):
        if 0 <= x < self.width and 0 <= y < self.height:
            return self.occupied_positions[y][x]
        return True  # Treat positions outside the layout area as occupied

    def is_position_valid(self, x, y):
        return not self.is_position_occupied(x, y)

# Check if a point is inside a polygon using the ray casting algorithm
def is_inside_polygon(x, y, polygon):
    num_vertices = len(polygon)
    inside = False
    for i in range(num_vertices):
        j = (i + 1) % num_vertices
        x1, y1 = polygon[i]
        x2, y2 = polygon[j]

        if intersects_horizontal_line(x1, y1, x2, y2, y):
            intersect_x = x1 + (y - y1) / (y2 - y1) * (x2 - x1)
            if intersect_x < x:
                inside = not inside
    return inside

# Check if a horizontal ray at y intersects segment (x1, y1)-(x2, y2)
def intersects_horizontal_line(x1, y1, x2, y2, y):
    if y1 > y2:
        y1, y2 = y2, y1
        x1, x2 = x2, x1
    return y1 <= y < y2  # Strict upper bound to avoid double counting

# Counter-clockwise test for orientation
def ccw(A, B, C):
    return (C[1] - A[1]) * (B[0] - A[0]) > (B[1] - A[1]) * (C[0] - A[0])

# Check if two line segments AB and CD intersect
def intersects_line_segment(x1, y1, x2, y2, x3, y3, x4, y4):
    A = (x1, y1)
    B = (x2, y2)
    C = (x3, y3)
    D = (x4, y4)
    return ccw(A, C, D) != ccw(B, C, D) and ccw(A, B, C) != ccw(A, B, D)

def intersects_room_boundary(room_polygons, furniture_polygons):
    # Check intersections between room boundaries
    for i in range(len(room_polygons)):
        poly1 = room_polygons[i]
        for j in range(i + 1, len(room_polygons)):
            poly2 = room_polygons[j]
            if poly1.intersects(poly2):
                return True

    # Check intersections between room boundaries and furniture
    for room_poly in room_polygons:
        for furn_poly in furniture_polygons:
            if room_poly.intersects(furn_poly):
                return True

    # Check intersections between furniture polygons
    for i in range(len(furniture_polygons)):
        poly1 = furniture_polygons[i]
        for j in range(i + 1, len(furniture_polygons)):
            poly2 = furniture_polygons[j]
            if poly1.intersects(poly2):
                return True

    return False

def intersects_furniture(furniture1, furniture2):
    # Check bounding box intersection
    x1_min, y1_min = min(furniture1.vertices, key=lambda v: v[0])[0], min(furniture1.vertices, key=lambda v: v[1])[1]
    x1_max, y1_max = max(furniture1.vertices, key=lambda v: v[0])[0], max(furniture1.vertices, key=lambda v: v[1])[1]
    x2_min, y2_min = min(furniture2.vertices, key=lambda v: v[0])[0], min(furniture2.vertices, key=lambda v: v[1])[1]
    x2_max, y2_max = max(furniture2.vertices, key=lambda v: v[0])[0], max(furniture2.vertices, key=lambda v: v[1])[1]

    if (x1_max < x2_min or x1_min > x2_max or
            y1_max < y2_min or y1_min > y2_max):
        # Bounding boxes do not intersect
        return False

    # Perform detailed intersection check
    for i in range(len(furniture1.vertices)):
        j = (i + 1) % len(furniture1.vertices)
        for k in range(len(furniture2.vertices)):
            l = (k + 1) % len(furniture2.vertices)
            if intersects_line_segment(*furniture1.vertices[i], *furniture1.vertices[j],
                                       *furniture2.vertices[k], *furniture2.vertices[l]):
                return True

    return False
        
# Define the constraint function
def no_intersections_constraint(positions):
    # Create furniture objects using the positions
    furniture_list = [
        Furniture([[pos[0], pos[1]], [pos[0] + 1, pos[1]], [pos[0] + 1, pos[1] + 1], [pos[0], pos[1] + 1]])
        for pos in positions]
    room_concave_hull = room_concave_hull
    # Check for intersection constraints
    if intersects_room_boundary([room_concave_hull], furniture_list):
        return -1.0  # Constraint violated
    else:
        return 0.0  # Constraint satisfied

# Add the constraint to a list
constraints = [{'type': 'ineq', 'fun': no_intersections_constraint, 'name': 'no_intersections_constraint'}]

# Define function to validate new positions and prevent intersections or placement inside other polygons
def validate_new_position(layout, x, y, furniture, room):
    if layout.is_position_valid(x, y):
        room_poly = room.offset_polygon
        furniture_poly = Polygon(furniture.vertices)  # ✅ Wrap as Geometry

        if intersects_room_boundary([room_poly], [furniture_poly]):
            return False

        for other_furniture in room.furniture:
            if Point(x, y).within(Polygon(other_furniture.vertices)):
                return False
            if intersects_room_boundary([furniture_poly], [Polygon(other_furniture.vertices)]):
                return False

        return True
    return False


# Function to calculate the length of a travel line based on its vertices
def calculate_travel_line_length(travel_line):
    num_vertices = len(travel_line)
    length = 0.0
    for i in range(num_vertices):
        j = (i + 1) % num_vertices
        length += np.linalg.norm(np.array(travel_line[i]) - np.array(travel_line[j]))
    return length

# File path for the CSV file containing rooms data
csv_file_path2 = r'C:\Users\user\Downloads\rooms_data.csv'  # Adjust the file path accordingly
# Read rooms data from CSV file
rooms = read_rooms_from_csv(csv_file_path2)
for room in rooms:
    if not room.offset_polygon or room.offset_polygon.is_empty:
        if hasattr(room, 'concave_hull_vertices') and room.concave_hull_vertices:
            try:
                room.offset_polygon = Polygon(room.concave_hull_vertices)
                print(f"[Fixed] Generated offset_polygon from concave hull for room {room.room_name}.")
            except Exception as e:
                print(f"[Error] Failed to create Polygon for {room.room_name} from concave hull: {e}")
        else:
            print(f"[Error] Room {room.room_name} has no geometry and no concave hull.")


# Generate travel lines between furniture
travel_lines_furniture = find_travel_lines_between_furniture(furniture_list, visibility_graph_furniture)

# Calculate lengths of travel lines for furniture
travel_line_lengths_furniture = [calculate_travel_line_length(travel_line_furniture) for travel_line_furniture in travel_lines_furniture]

# Find travel lines between rooms
travel_lines_rooms = find_travel_lines_between_rooms(rooms,visibility_graph_rooms)
# Calculate lengths of travel lines for rooms
travel_line_lengths_rooms = [calculate_travel_line_length(travel_line_room) for travel_line_room in travel_lines_rooms]
# Define the lengths and standard deviations for both furniture and rooms
if travel_line_lengths_furniture:
    mean_travel_line_length_furniture = np.mean(travel_line_lengths_furniture)
    travel_line_std_dev_furniture = np.std(travel_line_lengths_furniture)
else:
    mean_travel_line_length_furniture = 0
    travel_line_std_dev_furniture = 0

if travel_line_lengths_rooms:
    mean_travel_line_length_rooms = np.mean(travel_line_lengths_rooms)
    travel_line_std_dev_rooms = np.std(travel_line_lengths_rooms)
else:
    mean_travel_line_length_rooms = 0
    travel_line_std_dev_rooms = 0


# --- Proximity CSV generation ---
def write_proximity_csv(names, matrix, filename):
    with open(filename, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['item1', 'item2', 'proximity'])
        for i, a in enumerate(names):
            for j, b in enumerate(names):
                if i < j:
                    w.writerow([a, b, matrix[i][j]])

# Example: furniture proximity
write_proximity_csv(
    furniture_names,
    proximity_matrix_furniture,
    'furniture_proximity.csv'
)
write_proximity_csv(
    [r.room_name for r in rooms],
    proximity_matrix_rooms,
    'room_proximity.csv'
)

# --- Visibility Graph + Doorline start/goal collection ---
def gather_offset_door_vertices(furn_list):
    verts = []
    for f in furn_list:
        for dl in f.offset_doorlines:
            verts.extend(dl)
    return set(verts)

start_goal_vertices_f = gather_offset_door_vertices(furniture_list)
start_goal_vertices_r = gather_offset_door_vertices(
    sum((r.furniture for r in rooms), [])
)

def build_visibility_graph(all_verts, obstacles):
    G = {v: [] for v in all_verts}
    for a in all_verts:
        for b in all_verts:
            if a!=b and not any(
                    Polygon(obs).buffer(0).intersects(LineString([a,b]))
                    for obs in obstacles):
                G[a].append(b)
    return G

# Prepare obstacles: offset_polygons of furniture/rooms
all_f_obs = [f.offset_polygon for f in furniture_list]
all_r_obs = [r.offset_polygon for r in rooms]

Gf = build_visibility_graph(start_goal_vertices_f, all_f_obs)
Gr = build_visibility_graph(start_goal_vertices_r, all_r_obs)

# --- A* path ---
def euclid(a,b): return math.hypot(a[0]-b[0], a[1]-b[1])
def astar(G, s, t):
    pq, seen, P, cost = [(0,s)], set(), {s:None}, {s:0}
    while pq:
        g,u = heapq.heappop(pq)
        if u==t: break
        if u in seen: continue
        seen.add(u)
        for v in G[u]:
            ng = cost[u] + euclid(u,v)
            if ng < cost.get(v,1e9):
                cost[v]=ng; P[v]=u
                heapq.heappush(pq, (ng+euclid(v,t), v))
    path=[]
    u=t
    while u:
        path.append(u); u=P[u]
    return path[::-1]

# --- Build travel lines dicts ---
travel_f = {}
for f1 in furniture_list:
    for f2 in furniture_list:
        if f1!=f2:
            for s in f1.offset_doorlines:
                for g in f2.offset_doorlines:
                    for sv in s:
                        for gv in g:
                            path = astar(Gf, sv, gv)
                            if path:
                                travel_f[(f1,f2,sv,gv)] = LineString(path)

travel_r = {}
for r1 in rooms:
    for r2 in rooms:
        if r1!=r2:
            for f1 in r1.furniture:
                for f2 in r2.furniture:
                    for s in f1.offset_doorlines:
                        for g in f2.offset_doorlines:
                            for sv in s:
                                for gv in g:
                                    path = astar(Gr, sv, gv)
                                    if path:
                                        travel_r[(r1,r2,sv,gv)] = LineString(path)

def angle_between(v1, v2):
    v1 = np.array(v1) / np.linalg.norm(v1)
    v2 = np.array(v2) / np.linalg.norm(v2)
    return math.acos(np.clip(np.dot(v1, v2), -1.0, 1.0))

def calculate_angle_constraints(vertices, desired_angles, max_deviation=0.1):
    angles = []
    n = len(vertices)
    for i in range(n):
        v1 = np.subtract(vertices[i - 1], vertices[i])
        v2 = np.subtract(vertices[(i + 1) % n], vertices[i])
        angles.append(angle_between(v1, v2))
    return sum(abs(a - da) for a, da in zip(angles, desired_angles))
# CONFIGURABLE PARAMETERS
# ==============================
MIN_TRAVEL_LINE_WIDTH = 0.8  # meters
TRAVEL_LINE_INCREMENT = 0.2  # meters per step
MAX_TOTAL_AREA = 100000.0  # upper bound for combined area (rooms + travel lines)

# ==============================
# VENTILATION CONSTRAINTS
# ==============================
def calculate_ventilation_wall_ratio(polygon: Polygon, external_buffer=6.0):
    exterior = list(polygon.exterior.coords)
    good_walls = 0
    for i in range(len(exterior) - 1):
        mid = [(exterior[i][0] + exterior[i+1][0]) / 2, (exterior[i][1] + exterior[i+1][1]) / 2]
        normal = np.array([exterior[i+1][1] - exterior[i][1], -(exterior[i+1][0] - exterior[i][0])])
        normal = normal / np.linalg.norm(normal) * external_buffer
        projected = Point(mid[0] + normal[0], mid[1] + normal[1])
        line = LineString([mid, (projected.x, projected.y)])
        if not polygon.contains(projected):
            good_walls += 1
    return good_walls / (len(exterior) - 1)

def right_angle_constraint(room, tolerance_deg=5):
    coords = list(room.offset_polygon.exterior.coords)
    n = len(coords) - 1  # last == first
    penalty = 0
    for i in range(n):
        a = np.array(coords[i-1])
        b = np.array(coords[i])
        c = np.array(coords[(i+1)%n])
        ba = a - b
        bc = c - b
        cosine_angle = np.dot(ba, bc) / (np.linalg.norm(ba) * np.linalg.norm(bc))
        angle = np.arccos(np.clip(cosine_angle, -1.0, 1.0))
        angle_deg = np.degrees(angle)
        penalty += abs(angle_deg - 90)
    # Constraint: total penalty should be less than allowed deviation per corner
    return tolerance_deg * n - penalty  # Should be >= 0 for constraint satisfaction

# ==============================
# OBJECTIVE & CONSTRAINTS
# ==============================
def minimize_area_objective(rooms):
    return sum(room.offset_polygon.area for room in rooms)

def total_travel_line_length(travel_lines):
    return sum(LineString(line).length for line in travel_lines)

def total_area_objective(rooms, travel_lines):
    room_area = sum(shoelace_formula(list(room.offset_polygon.exterior.coords)) for room in rooms)
    travel_line_area = len(travel_lines) * (MIN_TRAVEL_LINE_WIDTH + TRAVEL_LINE_INCREMENT)**2
    return room_area + travel_line_area

def ventilation_constraint(rooms, threshold=0.5):
    for room in rooms:
        ratio = calculate_ventilation_wall_ratio(room.offset_polygon)
        if ratio < threshold:
            return threshold - ratio  # return positive if violated
    return 0.0

def angle_constraint(rooms, desired_angles_per_room):
    deviation = 0.0
    for room in rooms:
        if room.room_name in desired_angles_per_room:
            deviation += calculate_angle_constraints(
                list(room.offset_polygon.exterior.coords)[:-1],
                desired_angles_per_room[room.room_name]
            )
    return deviation

def no_overlap_constraint(rooms, furniture_list):
    for i, a in enumerate(rooms + furniture_list):
        for b in (rooms + furniture_list)[i+1:]:
            if a.offset_polygon.intersects(b.offset_polygon):
                return -1.0  # Constraint violated
    return 1.0

travel_lines = []
for key, line in travel_lines_between_rooms.items():
    room1, room2, start, end = key
    travel_lines.append({'rooms': (room1.room_name, room2.room_name), 'start': start, 'end': end})

for key, line in travel_lines_between_furniture.items():
    furniture1, furniture2, start, end = key
    travel_lines.append({'rooms': (furniture1.room, furniture2.room), 'start': start, 'end': end})

room_names = [room.room_name for room in rooms]

def proximity_penalty(rooms, proximity_matrix, travel_lines, room_names):
    """
    rooms: list of Room objects
    proximity_matrix: 2D list or numpy array of user-specified proximities
    travel_lines: dict with (room1, room2) tuple as key and LineString as value
    room_names: list of room names in the same order as proximity_matrix
    """
    n = len(room_names)
    diffs = []
    for i in range(n):
        for j in range(i+1, n):
            r1, r2 = room_names[i], room_names[j]
            prox = proximity_matrix[i][j]
            # Find the travel line between these rooms
            line = travel_lines.get((r1, r2)) or travel_lines.get((r2, r1))
            if line is not None:
                length = line.length
                diffs.append(abs(prox - length))
    return np.mean(diffs) if diffs else 0.0

def gather_doorline_endpoints(entities):
    endpoints = []
    for ent in entities:
        for doorline in getattr(ent, 'offset_doorlines', []):
            endpoints.extend(doorline)
    return endpoints
from shapely.geometry import LineString

def build_travel_lines(entities, min_width=0.8):
    """
    entities: list of Room or Furniture objects with offset_doorlines
    Returns: dict with (entity1, entity2) as key and LineString as value
    """
    travel_lines = {}
    for i, e1 in enumerate(entities):
        for j, e2 in enumerate(entities):
            if i < j:
                for dl1 in getattr(e1, 'offset_doorlines', []):
                    for dl2 in getattr(e2, 'offset_doorlines', []):
                        for p1 in dl1:
                            for p2 in dl2:
                                line = LineString([p1, p2])
                                # Check if the corridor (buffered line) is wide enough everywhere
                                corridor = line.buffer(min_width/2, cap_style=2)
                                # Optionally: check for intersections with obstacles here
                                travel_lines[(e1.room_name, e2.room_name)] = line
    return travel_lines

def combined_objective(rooms, travel_lines, area_weight=1.0, travel_weight=1.0, perimeter_weight=1, proximity_weight=1.0):
    area = minimize_area_objective(rooms)
    travel = total_travel_line_length(travel_lines)
    all_room_polys = [r.offset_polygon for r in rooms if r.offset_polygon]
    merged = unary_union(all_room_polys)
    perimeter = merged.length
    prox_penalty = proximity_penalty(rooms, proximity_matrix_rooms, travel_lines, room_names)
    return area_weight * area + perimeter_weight * perimeter + proximity_weight * prox_penalty

for room in rooms:
    # Generate travel lines for this room (if not already done)
    # travel_lines = ... (your logic here)
    points = collect_room_points(room, travel_lines)
    if len(points) < 3:
        print(f"[Error] Room {room.room_name} does not have enough points for a concave hull.")
        room.concave_hull = None
        room.offset_polygon = None
        continue
    try:
        hull = alphashape.alphashape(points, 0.5)
        if hull is None or hull.is_empty or hull.geom_type != 'Polygon':
            raise ValueError("Concave hull creation failed.")
        room.concave_hull = list(hull.exterior.coords)
        room.offset_polygon = hull
    except Exception as e:
        print(f"[Error] Room {room.room_name} hull creation failed: {e}")
        room.concave_hull = None
        room.offset_polygon = None

#function to populate rooms with furniture.
def populate_rooms_with_furniture(rooms, furniture_data):
    # Iterate over each room
    for room in rooms:
        # Clear existing furniture in the room
        room.furniture = []

        # Iterate over each furniture item in the furniture data
        for data in furniture_data:
            furniture_name, function, length, width, length_door, width_door, num_length_door, num_width_door = data

            # Check if any of the functions of the furniture match the functions of the room
            if any(func.strip() == function for func in room.functions):
                # Create a new Furniture object
                furniture = Furniture(furniture_name, function, length, width, length_door, width_door, num_length_door,
                                      num_width_door)

                # Add the furniture to the current room
                room.add_furniture(furniture)

        # Generate initial positions for furniture in the room
        room.generate_initial_positions(layout_width, layout_height)

        # Collect furniture vertices for the room
        furniture_vertices = room.collect_furniture_vertices()

        if furniture_vertices:  # Check if furniture vertices are not empty
            # Create concave hull for the room
            points = collect_room_points(room, travel_lines)
            if len(points) < 3:
                print(f"[Error] Room {room.room_name} does not have enough points for a concave hull.")
                room.concave_hull = None
                room.offset_polygon = None
                continue
            for furn in getattr(room, 'furniture', []):
                if hasattr(furn, 'vertices') and furn.vertices:
                    points.extend(furn.vertices)
            # Optionally, add travel line endpoints here if needed

            if len(points) < 3:
                print(f"[Error] Room {room.room_name} does not have enough points for a concave hull.")
                room.concave_hull = None
                room.offset_polygon = None
                continue

            try:
                concave_hull = alphashape.alphashape(points, 0.5)
                if concave_hull is None or concave_hull.is_empty or concave_hull.geom_type != 'Polygon':
                    # Fallback to convex hull if concave hull fails
                    concave_hull = MultiPoint(points).convex_hull
                    print(f"[Fallback] Used convex hull for room {room.room_name}.")
                room.concave_hull = concave_hull
                room.offset_polygon = concave_hull.buffer(1.1)  # or your desired offset
                print(f"[OK] Room {room.room_name} concave hull created.")
            except Exception as e:
                print(f"[Error] Room {room.room_name} hull creation failed: {e}")
                room.concave_hull = None
                room.offset_polygon = None
            room.set_vertices(concave_hull)  # Set concave hull vertices for the room
            print(f"Concave hull for Room {room.room_name}: {concave_hull}")
            # Print vertices of the furniture
            for furniture in room.furniture:
                print(f"Vertices of {furniture.furniture_name}: {furniture.vertices}")
        else:
            print(f"No furniture vertices found for Room {room.room_name}")

        # Associate furniture with rooms based on their positions
        for furniture in room.furniture:
            for other_room in rooms:
                if other_room != room:
                    # Check if the furniture position is within the other room's boundary
                    if Point(furniture.vertices[0]).within(Polygon(other_room.vertices)):
                        furniture.room = other_room
                        break

# Populate rooms with furniture based on matching function names
populate_rooms_with_furniture(rooms, furniture_data)
if room.concave_hull and hasattr(room.concave_hull, 'exterior'):
    coords = list(room.concave_hull.exterior.coords)

from shapely.geometry import Polygon

def is_valid_room(room, other_rooms=[]):
    poly = room.offset_polygon
    if poly is None or poly.is_empty or poly.geom_type != 'Polygon':
        return False
    if not poly.is_valid:
        return False
    # Check intersection with other rooms
    for other in other_rooms:
        if other != room and poly.intersects(other.offset_polygon):
            return False
    return True
def is_furniture_within_room(room):
    room_poly = room.offset_polygon
    for furniture in getattr(room, 'furniture', []):
        furn_poly = Polygon(furniture.vertices)
        if not room_poly.contains(furn_poly):
            print(f"Furniture {furniture.furniture_name} is not fully inside {room.room_name}")
            return False
    return True
def is_ventilated(room, threshold=0.5):
    ratio = calculate_ventilation_wall_ratio(room.offset_polygon)
    return ratio >= threshold
def is_right_angled(room, tolerance_deg=5):
    result = right_angle_constraint(room, tolerance_deg)
    return result >= 0
def validate_room(room, all_rooms):
    if not is_valid_room(room, all_rooms):
        print(f"[INVALID] Room {room.room_name} has bad geometry or overlaps.")
        return False
    if not is_furniture_within_room(room):
        print(f"[INVALID] Furniture in {room.room_name} are not contained properly.")
        return False
    if not is_ventilated(room):
        print(f"[INVALID] Room {room.room_name} has poor ventilation.")
        return False
    if not is_right_angled(room):
        print(f"[INVALID] Room {room.room_name} does not meet right-angle constraints.")
        return False
    return True

def build_travel_lines(rooms, graph_rooms):
    travel_lines = []
    for i, room1 in enumerate(rooms):
        for j, room2 in enumerate(rooms):
            if i < j:
                for dl1 in room1.offset_doorlines:
                    for dl2 in room2.offset_doorlines:
                        try:
                            path = a_star(graph_rooms, dl1[0], dl2[0])
                            if path:
                                travel_lines.append((room1, room2, LineString(path)))
                        except:
                            continue
    return travel_lines

def compute_weighted_travel_cost(travel_lines, proximity_weights, room_indices):
    total_cost = 0.0
    for (room1, room2, line) in travel_lines:
        length = line.length
        i = room_indices[room1.room_name]
        j = room_indices[room2.room_name]
        weight = proximity_weights[i][j]
        total_cost += weight * length
    return total_cost

def no_room_intersections_constraint(rooms):
    for i, room1 in enumerate(rooms):
        for j, room2 in enumerate(rooms):
            if i < j:
                if room1.offset_polygon and room2.offset_polygon:
                    if room1.offset_polygon.intersects(room2.offset_polygon):
                        return -1.0  # Violation
    return 1.0  # OK

# ==============================
# OPTIMIZATION CALL
# ==============================
def run_optimization(rooms, travel_lines, furniture_list, desired_angles_per_room):
    def objective(x):
        print(f"Evaluating objective at x={x}")
        return combined_objective(rooms, travel_lines, area_weight=1.0, travel_weight=1.0, perimeter_weight=1.0, proximity_weight=1.0)
    constraints = [
        {'type': 'ineq', 'fun': lambda x: ventilation_constraint(rooms)},
        {'type': 'ineq', 'fun': lambda x: angle_constraint(rooms, desired_angles_per_room)},
        {'type': 'ineq', 'fun': lambda x: no_overlap_constraint(rooms, furniture_list)},
        {'type': 'ineq', 'fun': lambda x: MAX_TOTAL_AREA - total_area_objective(rooms, travel_lines)},
        {'type': 'ineq', 'fun': lambda x: no_overlap_constraint(rooms, furniture_list)},
        {'type': 'ineq', 'fun': lambda x: no_room_intersections_constraint(rooms)}
    ]
    for room in rooms:
        constraints.append({'type': 'ineq', 'fun': lambda x, r=room: right_angle_constraint(r)})
# Add other constraints as needed (e.g., furniture containment)
    x0 = 1
    result = minimize(objective, x0, constraints=constraints, options={'maxiter': 10000,
    'disp': True,
    'fatol': 1e-6,})
    return result, travel_lines

for room in rooms:
    if room.offset_polygon:
        print(f"[OK] Room {room.room_name} offset polygon vertices: {list(room.offset_polygon.exterior.coords)}")
    else:
        print(f"[Missing] Room {room.room_name} has no valid offset polygon.")
for room in rooms:
    if not is_valid_room(room, rooms):
        print(f"[Warning] Room {room.room_name} is still intersecting or invalid.")

def update_room_points_from_furniture(room):
    """
    Collects all furniture vertices in the room and updates room.vertices.
    """
    points = []
    for furn in getattr(room, 'furniture', []):
        if hasattr(furn, 'vertices') and furn.vertices:
            points.extend(furn.vertices)
    room.vertices = points 

for room in rooms:
    # 1. Collect all current furniture vertices
    points = []
    for furn in getattr(room, 'furniture', []):
        if hasattr(furn, 'vertices') and furn.vertices:
            points.extend(furn.vertices)
    room.vertices = points

    # 2. Check and create hull/polygon
    if len(room.vertices) >= 3:
        hull = alphashape.alphashape(room.vertices, 0.5)
        if hull and not hull.is_empty and hull.geom_type == 'Polygon':
            room.concave_hull = list(hull.exterior.coords)
            room.offset_polygon = Polygon(room.concave_hull)
        else:
            print(f"[Error] Room {room.room_name} hull creation failed after optimization.")
            room.concave_hull = None
            room.offset_polygon = None
    else:
        print(f"[Error] Room {room.room_name} does not have enough points after optimization.")
        room.concave_hull = None
        room.offset_polygon = None
          
# ==============================
# PLOTTING
# ==============================

def plot_and_save_layout(rooms, travel_lines, filename="optimized_layout.png"):
    import matplotlib.pyplot as plt
    import os
    plt.figure(figsize=(10, 10))
    ax = plt.gca()

    # Plot Rooms & Furniture
    for room in rooms:
        poly = getattr(room, 'offset_polygon', None)
        if poly is None or poly.is_empty:
            continue
        x, y = poly.exterior.xy
        ax.plot(x, y, 'b-', linewidth=2)
        ax.fill(x, y, alpha=0.15, color='blue')
        centroid = poly.centroid
        ax.text(centroid.x, centroid.y, room.room_name, fontsize=12, color='navy', ha='center')

        # Plot Room Doorlines
        for dl in getattr(room, 'offset_doorlines', []):
            for p in dl:
                ax.plot(*zip(*dl), color='orange', linewidth=3, label='Room Doorline')

        # Plot Furniture
        for furn in room.furniture:
            fx, fy = zip(*furn.vertices)
            ax.plot(fx, fy, 'r-', linewidth=1)
            ax.fill(fx, fy, alpha=0.3, color='red')
            ax.text(np.mean(fx), np.mean(fy), furn.furniture_name, fontsize=9, color='darkred', ha='center')
            
            # Plot Furniture Doorlines
            for dl in getattr(furn, 'offset_doorlines', []):
                for p in dl:
                    ax.plot(*zip(*dl), color='orange', linewidth=2, linestyle='--')

    # Plot Travel Lines
    for line in travel_lines:
        if isinstance(line, LineString):
            x, y = line.xy
            ax.plot(x, y, 'g--', linewidth=2, alpha=0.7, label='Travel Line')

    ax.set_aspect('equal')
    ax.set_title("Optimized Layout with Travel and Doorlines")
    ax.axis('off')

    # Save PNG
    downloads = os.path.join(os.path.expanduser("~"), "Downloads")
    path = os.path.join(downloads, filename)
    plt.savefig(path, bbox_inches='tight', dpi=300)
    print(f"Plot saved to: {path}")
    plt.show()


def main():

    # 1. Load CSV Data
    csv_file_path2 = r'C:\Users\user\Downloads\rooms_data.csv'
    rooms = read_rooms_from_csv(csv_file_path2)

    # 2. Create Furniture and Assign to Rooms
    populate_rooms_with_furniture(rooms, furniture_data)

    # 3. Create Concave Hulls for Rooms
    for room in rooms:
        if not room.offset_polygon or room.offset_polygon.is_empty:
            if hasattr(room, 'concave_hull_vertices') and room.concave_hull_vertices:
                try:
                    room.offset_polygon = Polygon(room.concave_hull_vertices)
                    print(f"[Fixed] Generated offset_polygon from concave hull for room {room.room_name}.")
                except Exception as e:
                    print(f"[Error] Failed to create Polygon for {room.room_name} from concave hull: {e}")
            else:
                print(f"[Error] Room {room.room_name} has no geometry and no concave hull.")

    # 4. Build Travel Lines
    # Assume these have been properly constructed earlier in your code
    start_goal_vertices_f = gather_offset_door_vertices(furniture_list)
    all_furniture_obstacles = [f.offset_polygon for f in furniture_list if f.offset_polygon]

    # Now call with both arguments
    visibility_graph_f = build_visibility_graph(start_goal_vertices_f, all_furniture_obstacles)

    
    travel_lines_f = find_travel_lines_between_furniture(furniture_list, visibility_graph_f)

    start_goal_vertices_r = gather_offset_door_vertices(sum((r.furniture for r in rooms), []))
    all_room_obstacles = [r.offset_polygon for r in rooms if r.offset_polygon]

    visibility_graph_r = build_visibility_graph(start_goal_vertices_r, all_room_obstacles)

    travel_lines_r = find_travel_lines_between_rooms(rooms, visibility_graph_r)

    # 5. Evaluate Geometry and Constraints
    for furniture in room.furniture:
        for x in range(layout.width):
            for y in range(layout.height):
                if validate_new_position(layout, x, y, furniture, room):
                    print(f"Furniture {furniture.furniture_name} can be placed at ({x}, {y}) in room {room.room_name}")
    for room in rooms:
        if validate_room(room, rooms):
            print(f"[OK] Room {room.room_name} is valid.")
        else:
            print(f"[FAIL] Room {room.room_name} failed validation.")


    # 6. Run Optimization
    desired_angles_per_room = {
        room.room_name: [np.pi / 2] * len(room.offset_polygon.exterior.coords[:-1])
        for room in rooms if room.offset_polygon
    }
    result, travel_lines = run_optimization(
    rooms, travel_lines_r, furniture_list, desired_angles_per_room
    )

    # 7. Plot Result
    plot_and_save_layout(rooms, list(travel_lines_r.values()))


if __name__ == "__main__":
    main()

def export_to_geojson(rooms, travel_lines, filename="layout.geojson"):
    features = []

    # Rooms
    for room in rooms:
        if room.offset_polygon:
            features.append(geojson.Feature(
                geometry=mapping(room.offset_polygon),
                properties={"type": "room", "name": room.room_name}
            ))
        for furn in room.furniture:
            features.append(geojson.Feature(
                geometry=geojson.Polygon([furn.vertices]),
                properties={"type": "furniture", "name": furn.furniture_name}
            ))
            for dl in getattr(furn, 'offset_doorlines', []):
                features.append(geojson.Feature(
                    geometry=geojson.LineString(dl),
                    properties={"type": "doorline", "parent": furn.furniture_name}
                ))

    # Travel lines
    for line in travel_lines:
        if isinstance(line, LineString):
            features.append(geojson.Feature(
                geometry=mapping(line),
                properties={"type": "travel_line"}
            ))

    feature_collection = geojson.FeatureCollection(features)
    downloads = os.path.join(os.path.expanduser("~"), "Downloads")
    path = os.path.join(downloads, filename)
    with open(path, 'w') as f:
        geojson.dump(feature_collection, f)
    print(f"GeoJSON exported to: {path}")

def export_to_dxf(rooms, travel_lines, filename="layout.dxf"):
    doc = ezdxf.new()
    msp = doc.modelspace()

    for room in rooms:
        if room.offset_polygon:
            points = list(room.offset_polygon.exterior.coords)
            msp.add_lwpolyline(points, close=True, dxfattribs={"layer": "Rooms"})
        for furn in room.furniture:
            msp.add_lwpolyline(furn.vertices, close=True, dxfattribs={"layer": "Furniture"})
            for dl in getattr(furn, 'offset_doorlines', []):
                msp.add_lwpolyline(dl, dxfattribs={"layer": "FurnitureDoorlines"})

        for dl in getattr(room, 'offset_doorlines', []):
            msp.add_lwpolyline(dl, dxfattribs={"layer": "RoomDoorlines"})

    for line in travel_lines:
        if isinstance(line, LineString):
            msp.add_lwpolyline(list(line.coords), dxfattribs={"layer": "TravelLines"})

    downloads = os.path.join(os.path.expanduser("~"), "Downloads")
    path = os.path.join(downloads, filename)
    doc.saveas(path)
    print(f"DXF exported to: {path}")
